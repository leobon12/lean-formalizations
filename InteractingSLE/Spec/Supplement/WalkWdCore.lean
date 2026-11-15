/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkWdPair
import InteractingSLE.Spec.Supplement.WalkWordsCompWire

/-!
# The finite-word matches of one component chart (per sample)

Packet PROVE-WALK-WORDS2. Deterministic assembly of `hMatch` (the binder of PROVE-T14-WALKINT's
`walkNormChartLocStatement_of_finite_matches`) for one sample, one component `C` and one component chart `c`, with
the canonical word `componentWord` (PROVE-WALK-WORDS):

* `IsControlledMatch s s' left c x p`: for every open `U ∋ p`, a recorded prefix of `s` with the complete prefix
  match at `x` (for every reference hull containing the prefix's hull) and a fresh point of the walk in `U` after the
  prefix (`WalkWd.exists_controlledMatch_right` / `_left` give it at landings in `ℍ`);
* **`finite_matches_of_sample`**: the exceptional set is `F = {0} ∪ ℓ⁻¹(pieceEnds R ∪ pieceEnds L ∪ jumps)`, finite
  since the landing map `ℓ` is injective. At `x ∉ F`, `x > 0`: the landing `p = ℓ(x)` is on the right walk and not on
  the left walk (`WalkWd.pocket_landing_facts`). If `p` is an ordinary point of the right walk, the controlled match
  and the closing contact give a `RetainedPair` with `BeforeExit` (`exists_retainedPair_right`), and the word is `−Λ`;
  otherwise `p` is a real point off both ordinary sets (the right one is closed, the left one lies in the left wall),
  hence a real match with the word `b(p)`. Mirror for `x < 0`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.WalkWd

open WalkBdry WalkMean WalkNorm WalkWords WalkIntFill WalkIntActive

/-- **A controlled prefix match** at `x` with landing `p` (see the module docstring). -/
def IsControlledMatch (s s' : ExplState) (left : Bool) (c : Chart) (x : ℝ) (p : ℂ) : Prop :=
  ∀ U : Set ℂ, IsOpen U → p ∈ U → ∃ (pre post : List Piece) (pc : Piece) (τ : ℚ≥0),
    s.1 = pre ++ pc :: post ∧ (((τ : ℝ≥0)) : ℝ≥0∞) < pc.2.2 ∧
    (∃ z ∈ U, z ∈ wsetOf s ∧ z ∉ prefixSet pre pc τ) ∧
    ∀ {d : Chart} (B : WalkIntCanon.HullModel d) (A : WalkIntCanon.HullModel (prefixChart pc τ)),
      A.hull ⊆ B.hull → WalkIntFiber.IsPiecePhysicalMatch s s' left c B x

/-- A point off the closures of both ordinary sets has a ball disjoint from both. -/
theorem exists_ball_disjoint_union {S T : Set ℂ} {q : ℂ} (hS : q ∉ closure S) (hT : q ∉ closure T) :
    ∃ r > 0, Disjoint (ball q r) (S ∪ T) := by
  have hq : q ∈ (closure (S ∪ T))ᶜ := by rw [closure_union]; exact fun h => h.elim hS hT
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl q hq
  exact ⟨r, hr, Set.disjoint_left.2 fun z hz hzS => hball hz (subset_closure hzS)⟩

open Classical in
/-- The word of `componentWord` at a landing. -/
theorem componentWord_of_landing {κ : ℝ} {b : ℝ → ℝ} {ordR ordL : Set ℂ} {inv : ℂ → ℂ} {x : ℝ} {p : ℂ}
    (hp : Tendsto inv (𝓝[H] (x : ℂ)) (𝓝 p)) :
    (0 < x → componentWord κ b ordR ordL inv x = if p ∈ ordR then -bigLambda κ else b p.re) ∧
    (x < 0 → componentWord κ b ordR ordL inv x = if p ∈ ordL then bigLambda κ else b p.re) := by
  have hx : ((x : ℂ)) ∈ closure H := by rw [closure_H]; show (0 : ℝ) ≤ ((x : ℂ)).im; simp
  have he : extendFrom H inv x = p := extendFrom_eq hx hp
  refine ⟨fun hx0 => ?_, fun hx0 => ?_⟩
  · simp only [componentWord, hx0, ↓reduceIte, he, bigLambda]
  · have hn : ¬ 0 < x := not_lt.2 hx0.le
    simp only [componentWord, hn, hx0, ↓reduceIte, he, bigLambda]

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {specR specL : ExplSpec} {sR sL : ExplState}
  {α β : ℝ≥0 → ℂ} {C : Set ℂ} {c : Chart}

/-- **The finite-word matches of one component chart** (see the module docstring). -/
theorem finite_matches_of_sample (hα : Supp9B.IsProperCurve α) (hβ : Supp9B.IsProperCurve β) (hα0 : α 0 = 0)
    (hβ0 : β 0 = 0) (hrR : range α = physOf specR sR) (hrL : range β = physOf specL sL)
    (hco : ∀ s s' t t' : ℝ≥0, α s = β t → α s' = β t' → (s < s' ↔ t < t')) (hW : GW4Reg.WalkPocketShape α β)
    (hC : C ∈ betweenComponents (physOf specR sR) (physOf specL sL))
    (hc : IsComponentChart (physOf specR sR) (physOf specL sL) C c) (hdom : (c.dom : Set ℂ) = C)
    {ℓ : ℝ → ℂ} (hℓi : Function.Injective ℓ) (hℓ : ∀ x : ℝ, Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 (ℓ x)))
    (hclR : IsClosed (ordOf sR)) (hclL : IsClosed (ordOf sL))
    (hctlR : ∀ (x : ℝ) (p : ℂ), 0 < x → Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 p) → p ∈ ordOf sR →
      p ∉ pieceEnds sR.1 → p ∉ closure (wsetOf sL) → IsControlledMatch sR sL true c x p)
    (hctlL : ∀ (x : ℝ) (p : ℂ), x < 0 → Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 p) → p ∈ ordOf sL →
      p ∉ pieceEnds sL.1 → p ∉ closure (wsetOf sR) → IsControlledMatch sL sR false c x p)
    (hmkR : ∀ (pre post : List Piece) (pc : Piece), sR.1 = pre ++ pc :: post → ∀ τ : ℝ≥0,
      (τ : ℝ≥0∞) < pc.2.2 → ∃ R : WalkPrefix sR, R.pre = pre ∧ R.post = post ∧ R.piece = pc ∧ R.time = τ)
    (hmkL : ∀ (pre post : List Piece) (pc : Piece), sL.1 = pre ++ pc :: post → ∀ τ : ℝ≥0,
      (τ : ℝ≥0∞) < pc.2.2 → ∃ R : WalkPrefix sL, R.pre = pre ∧ R.post = post ∧ R.piece = pc ∧ R.time = τ)
    (hrawR : ∀ R : WalkPrefix sR, ∃ a : ℝ≥0, R.raw = α '' Icc 0 a ∩ H)
    (hrawL : ∀ R : WalkPrefix sL, ∃ a : ℝ≥0, R.raw = β '' Icc 0 a ∩ H)
    (R₀ : WalkPrefix sR) (hR₀ : R₀.raw = ∅) (L₀ : WalkPrefix sL) (hL₀ : L₀.raw = ∅)
    {jumpsC : Finset ℝ} (hpw : IsPiecewiseConstantBoundaryData (componentWord κ b (ordOf sR) (ordOf sL) c.2.1) jumpsC)
    (hcbd : IsComponentBoundaryData κ b (ordOf sR) (ordOf sL) c.2.1
      (componentWord κ b (ordOf sR) (ordOf sL) c.2.1) jumpsC) :
    ∃ (t : Chart × (ℝ → ℝ) × Finset ℝ) (F : Set ℝ), F.Finite ∧
      IsComponentChart (physOf specR sR) (physOf specL sL) C t.1 ∧
      IsPiecewiseConstantBoundaryData t.2.1 t.2.2 ∧
      IsComponentBoundaryData κ b (ordOf sR) (ordOf sL) t.1.2.1 t.2.1 t.2.2 ∧
      ∀ x : ℝ, x ∉ F →
        (0 < x → ∃ J : RetainedPair sR sL,
          (((Bornology.IsBounded (t.1.dom : Set ℂ) → Nonempty (BeforeExit J (t.1.dom : Set ℂ) α β)) ∧
            WalkIntFiber.IsPiecePhysicalMatch sR sL true t.1 J.model x ∧ t.2.1 x = -bigLambda κ) ∨
            WalkIntGerm.IsRealIncidentMatch sR sL b jumps t.1 J.model x (t.2.1 x))) ∧
        (x < 0 → ∃ J : RetainedPair sR sL,
          (((Bornology.IsBounded (t.1.dom : Set ℂ) → Nonempty (BeforeExit J (t.1.dom : Set ℂ) α β)) ∧
            WalkIntFiber.IsPiecePhysicalMatch sL sR false t.1 J.model x ∧ t.2.1 x = bigLambda κ) ∨
            WalkIntGerm.IsRealIncidentMatch sR sL b jumps t.1 J.model x (t.2.1 x))) := by
  have hfα : GB11.IsCompleteSimpleFlow α := ⟨hα.1, hα.2.1, hα0, fun t => hα.2.2.1 t, hα.2.2.2⟩
  have hfβ : GB11.IsCompleteSimpleFlow β := ⟨hβ.1, hβ.2.1, hβ0, fun t => hβ.2.2.1 t, hβ.2.2.2⟩
  have hC' : C ∈ betweenComponents (range α) (range β) := by rw [hrR, hrL]; exact hC
  have hc' : IsComponentChart (range α) (range β) C c := by rw [hrR, hrL]; exact hc
  obtain ⟨hnot, hexit⟩ := pocket_landing_facts hfα hfβ hco hW hC' hc'
  have hαc : IsClosed (range α) := GW4Reg.isClosed_range_of_isCompleteSimpleFlow hfα
  have hβc : IsClosed (range β) := GW4Reg.isClosed_range_of_isCompleteSimpleFlow hfβ
  have hwR : wsetOf sR ⊆ range α := fun z hz => hrR ▸ Or.inl (Or.inr hz.1)
  have hwL : wsetOf sL ⊆ range β := fun z hz => hrL ▸ Or.inl (Or.inr hz.1)
  have hclwR : closure (wsetOf sR) ⊆ ordOf sR := closure_minimal (fun z hz => hz.1) hclR
  have hclwL : closure (wsetOf sL) ⊆ ordOf sL := closure_minimal (fun z hz => hz.1) hclL
  have hclwLβ : closure (wsetOf sL) ⊆ range β := closure_minimal hwL hβc
  have hclwRα : closure (wsetOf sR) ⊆ range α := closure_minimal hwR hαc
  -- the exceptional set
  set F : Set ℝ := {0} ∪ ℓ ⁻¹' (pieceEnds sR.1 ∪ pieceEnds sL.1 ∪ ((↑) : ℝ → ℂ) '' (jumps : Set ℝ)) with hFdef
  have hF : F.Finite := (finite_singleton 0).union
    ((((pieceEnds_finite _).union (pieceEnds_finite _)).union (jumps.finite_toSet.image _)).preimage
      hℓi.injOn)
  refine ⟨(c, componentWord κ b (ordOf sR) (ordOf sL) c.2.1, jumpsC), F, hF, hc, hpw, hcbd,
    fun x hxF => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  all_goals
    have hxF' : ℓ x ∉ pieceEnds sR.1 ∧ ℓ x ∉ pieceEnds sL.1 ∧ ℓ x ∉ ((↑) : ℝ → ℂ) '' (jumps : Set ℝ) :=
      ⟨fun h => hxF (Or.inr (Or.inl (Or.inl h))), fun h => hxF (Or.inr (Or.inl (Or.inr h))),
        fun h => hxF (Or.inr (Or.inr h))⟩
    obtain ⟨hpE, hpE', hpJ⟩ := hxF'
    obtain ⟨p₁, hp₁, hp₁R, hp₁L⟩ := hc.2.2.2.2.1 x
    have : (𝓝[H] (x : ℂ)).NeBot := GW1P.neBot_nhdsWithin_H (show (0 : ℝ) ≤ ((x : ℂ)).im by simp)
    have hpp : p₁ = ℓ x := tendsto_nhds_unique hp₁ (hℓ x)
    subst hpp
    obtain ⟨hw1, hw2⟩ := componentWord_of_landing (κ := κ) (b := b) (ordR := ordOf sR) (ordL := ordOf sL) (hℓ x)
    obtain ⟨hn1, hn2⟩ := hnot x (ℓ x) (hℓ x)
    obtain ⟨J₀, -, -⟩ := exists_retainedPair R₀ L₀
  · -- `x > 0`
    have hpR := hp₁R hx
    have hpβ := hn1 hx
    by_cases hpo : ℓ x ∈ ordOf sR
    · have hctl := hctlR x (ℓ x) hx (hℓ x) hpo hpE (fun h => hpβ (hclwLβ h))
      obtain ⟨J, hbe, hm⟩ := exists_retainedPair_right hα hα0 hβ0 (hrR ▸ hpR) hwR hctl hmkR hrawR L₀ hL₀
        (fun hb => by
          obtain ⟨U, V, hUV, hUC, hlt⟩ := hexit hb
          exact ⟨U, V, hUV, hUC, (hlt x (ℓ x) (hℓ x)).1⟩)
      refine ⟨J, Or.inl ⟨by rw [hdom]; exact hbe, hm, ?_⟩⟩
      show componentWord κ b (ordOf sR) (ordOf sL) c.2.1 x = _
      rw [hw1 hx, ite_eq_left hpo]
    · have him : (ℓ x).im = 0 := (mem_ordOf_or_im_eq_zero hpR).resolve_left hpo
      have hre : ((ℓ x).re : ℂ) = ℓ x := Complex.ext (by simp) (by simp [him])
      obtain ⟨r, hr, hgap⟩ := exists_ball_disjoint_union (S := wsetOf sR) (T := wsetOf sL) (q := ℓ x)
        (fun h => hpo (hclwR h)) (fun h => hpβ (hclwLβ h))
      refine ⟨J₀, Or.inr (J₀.isRealIncidentMatch (a := (ℓ x).re) (r := r)
        (fun h => hpJ ⟨_, h, hre⟩) hr (by rw [hre]; exact hℓ x) (by rw [hre]; exact hgap) ?_)⟩
      show componentWord κ b (ordOf sR) (ordOf sL) c.2.1 x = _
      rw [hw1 hx, ite_eq_right hpo]
  · -- `x < 0`
    have hpL := hp₁L hx
    have hpα := hn2 hx
    by_cases hpo : ℓ x ∈ ordOf sL
    · have hctl := hctlL x (ℓ x) hx (hℓ x) hpo hpE' (fun h => hpα (hclwRα h))
      obtain ⟨J, hbe, hm⟩ := exists_retainedPair_left hβ hα0 hβ0 (hrL ▸ hpL) hwL hctl hmkL hrawL R₀ hR₀
        (fun hb => by
          obtain ⟨U, V, hUV, hUC, hlt⟩ := hexit hb
          exact ⟨U, V, hUV, hUC, (hlt x (ℓ x) (hℓ x)).2⟩)
      refine ⟨J, Or.inl ⟨by rw [hdom]; exact hbe, hm, ?_⟩⟩
      show componentWord κ b (ordOf sR) (ordOf sL) c.2.1 x = _
      rw [hw2 hx, ite_eq_left hpo]
    · have him : (ℓ x).im = 0 := (mem_ordOf_or_im_eq_zero hpL).resolve_left hpo
      have hre : ((ℓ x).re : ℂ) = ℓ x := Complex.ext (by simp) (by simp [him])
      obtain ⟨r, hr, hgap⟩ := exists_ball_disjoint_union (S := wsetOf sR) (T := wsetOf sL) (q := ℓ x)
        (fun h => hpα (hclwRα h)) (fun h => hpo (hclwL h))
      refine ⟨J₀, Or.inr (J₀.isRealIncidentMatch (a := (ℓ x).re) (r := r)
        (fun h => hpJ ⟨_, h, hre⟩) hr (by rw [hre]; exact hℓ x) (by rw [hre]; exact hgap) ?_)⟩
      show componentWord κ b (ordOf sR) (ordOf sL) c.2.1 x = _
      rw [hw2 hx, ite_eq_right hpo]

end InteractingSLE.Theorem14.WalkWd

/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NeEnd

/-!
# F2b′'s relative facts at one sample

Packet PROVE-AUX61-NOJUMP (round 22, component F), deterministic. From D34's clause for an extension `g` of the
retained hull chart's inverse, the right entry chart at `R = max (X ∩ ℝ)` with offset `x₀`, and the physical facts of
B's piece (`R` and the piece before its lifetime off the closure of the original right-bad points right of `R`; at a
finite lifetime the piece ends at such a point; at an infinite lifetime the relative capacity is infinite):

* `exists_preimage_right`, `unique_preimage`: the free ray right of `R` has exactly one real preimage, right of `x₀`;
* **`endpoint_bad`**: at a finite relative lifetime the relative trace converges to a bad relative point;
* **`relFactsAt_of`**: the stops' `RelFactsAt` (cover, seed, avoidance, end).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar chiC)

namespace InteractingSLE.Theorem14.SB.Ne

open Sec7.PocketTraversal Sec7.Lemma71C Lk LuM Exist Exist.Staged Exist.StagedLaw Dv Nc Nd Vs Vr Lv Supp8.Q3Stop

section Pre

variable {X : Set ℂ} {g : ℂ → ℂ} {R x₀ : ℝ}

/-- **Every free real point right of `R` has a preimage right of `x₀`.** -/
theorem exists_preimage_right (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hR : g (x₀ : ℂ) = R)
    (hreal : ∀ y : ℝ, x₀ < y → (g (y : ℂ)).im = 0) {C : ℝ} (hC : ∀ q : ℂ, 0 ≤ q.im → ‖g q - q‖ ≤ C) {x : ℝ}
    (hx : R < x) : ∃ v : ℝ, x₀ < v ∧ g (v : ℂ) = x := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 (show (0 : ℝ) ≤ (0 : ℂ).im by simp))
  set Y : ℝ := max x₀ x + C + 1 with hY
  have hxY : x₀ ≤ Y := by have := le_max_left x₀ x; linarith
  have hφc : ContinuousOn (fun y : ℝ => (g (y : ℂ)).re) (Icc x₀ Y) :=
    Complex.continuous_re.comp_continuousOn
      (hgc.comp Complex.continuous_ofReal.continuousOn fun y _ => show (0 : ℝ) ≤ ((y : ℝ) : ℂ).im by simp)
  have hYx : x ≤ (g (Y : ℂ)).re := by
    have h := hC (Y : ℂ) (show (0 : ℝ) ≤ ((Y : ℝ) : ℂ).im by simp)
    have h2 := Complex.abs_re_le_norm (g (Y : ℂ) - (Y : ℂ))
    simp only [Complex.sub_re, Complex.ofReal_re] at h2
    have := le_max_right x₀ x
    have := neg_abs_le ((g (Y : ℂ)).re - Y)
    linarith
  have hR' : (g (x₀ : ℂ)).re = R := by rw [hR]; simp
  obtain ⟨v, hv, hvx⟩ := intermediate_value_Icc hxY hφc ⟨by rw [hR']; exact hx.le, hYx⟩
  have hv0 : x₀ < v := by
    refine lt_of_le_of_ne hv.1 fun h => ?_
    subst h
    simp only at hvx
    rw [hR'] at hvx
    linarith
  exact ⟨v, hv0, Complex.ext (by simpa using hvx) (by simp [hreal v hv0])⟩

/-- **The free ray right of `R` has exactly one preimage in `ℍ̄`.** -/
theorem unique_preimage (hA : IsHPHull (fillH X)) (hgc : ContinuousOn g {z | 0 ≤ z.im})
    (hgi : EqOn g (Mo.hullChart (fillH X) 0).2.1 H) (hR : g (x₀ : ℂ) = R)
    (hmono : StrictMonoOn (fun y : ℝ => (g (y : ℂ)).re) (Ici x₀)) {C : ℝ}
    (hC : ∀ q : ℂ, 0 ≤ q.im → ‖g q - q‖ ≤ C)
    (hfree : ∀ x : ℝ, R < x → ∃ r > 0, Disjoint (ball (x : ℂ) r) (fillH X)) {x v : ℝ} (hx : R < x)
    (hv : x₀ < v) (hgv : g (v : ℂ) = x) {z : ℂ} (hz : 0 ≤ z.im) (hgz : g z = x) : z = v := by
  rcases hz.lt_or_eq with him | him
  · exfalso
    have : g z ∈ H := by rw [hgi him]; exact (hullChart_inv_mem hA 0 him).1
    rw [hgz] at this
    exact absurd this (by show ¬ (0 : ℝ) < ((x : ℝ) : ℂ).im; simp)
  · have hze : z = ((z.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [← him])
    set w := z.re with hw
    rw [hze] at hgz ⊢
    rcases lt_trichotomy w x₀ with hlt | heq | hgt
    · exfalso
      -- the shifted chart, tip at `0`
      set c := Mo.hullChart (fillH X) x₀ with hc
      have hcc := Mo.isConformal_hullChart hA x₀
      set g' : ℂ → ℂ := fun z => g (z + x₀) with hg'
      have hgc' : ContinuousOn g' {z | 0 ≤ z.im} :=
        hgc.comp (continuous_id.add continuous_const).continuousOn fun z (hz : 0 ≤ z.im) =>
          show 0 ≤ (z + (x₀ : ℂ)).im by simpa using hz
      have hgi' : EqOn g' c.2.1 H := by
        intro z hz
        have hz' : z + (x₀ : ℂ) ∈ H := by show 0 < (z + (x₀ : ℂ)).im; simpa using (show 0 < z.im from hz)
        simp only [hg', hgi hz', hc, Mo.hullChart_inv, add_zero, Complex.ofReal_zero]
      have hprop : ∀ q : ℂ, 0 ≤ q.im → ‖q‖ ≤ 1 * ‖g' q‖ + (C + |x₀|) := fun q hq => by
        have h1 := hC (q + x₀) (by simpa using hq)
        have h2 : ‖q + (x₀ : ℂ)‖ ≤ ‖g' q‖ + C := by
          have := norm_sub_norm_le (q + (x₀ : ℂ)) (g' q)
          rw [norm_sub_rev] at h1
          linarith
        have h3 : ‖q‖ ≤ ‖q + (x₀ : ℂ)‖ + |x₀| := by
          have := norm_sub_le (q + (x₀ : ℂ)) (x₀ : ℂ)
          rw [add_sub_cancel_right, Complex.norm_real, Real.norm_eq_abs] at this
          exact this
        linarith
      have hg0 : g' 0 = R := by simp [hg', hR]
      obtain ⟨r, hr, hd⟩ := hfree x hx
      have hdom := (Mo.isDomainChart_hullChart hA x₀).2.1
      have hfr : ∀ z ∈ H, dist z (x : ℂ) < r → z ∈ c.2.1 '' H := fun z hz hdz => by
        rw [hdom]; exact ⟨hz, fun hF => Set.disjoint_left.1 hd (mem_ball.2 hdz) hF⟩
      have h0 : g' (((w - x₀ : ℝ)) : ℂ) = x := by simp only [hg']; push_cast; rw [sub_add_cancel]; exact hgz
      have h1 : g' (((v - x₀ : ℝ)) : ℂ) = x := by simp only [hg']; push_cast; rw [sub_add_cancel]; exact hgv
      exact not_two_sides hcc hgc' hgi' hprop hg0 (ne_of_gt hx) hr hfr (by linarith) (by linarith) h0 h1
    · exfalso
      rw [heq, hR] at hgz
      have : R = x := by exact_mod_cast hgz
      linarith
    · have h1 := hmono.injOn (show w ∈ Ici x₀ from hgt.le) (show v ∈ Ici x₀ from hv.le)
        (show (g (w : ℂ)).re = (g (v : ℂ)).re by rw [hgz, hgv])
      rw [h1]

end Pre


section Facts

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {X : Set ℂ} {g : ℂ → ℂ} {R x₀ : ℝ} {p : ℝ≥0 → ℂ} {L : ℝ≥0∞}
  {β : Restart.BoundaryWord} {Fy : Finset ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ}

/-- **At a finite relative lifetime the relative trace converges to a bad relative point right of the seed.** -/
theorem endpoint_bad (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps) (hA : IsHPHull (fillH X))
    (hL0 : L ≠ 0) (hpc : ContinuousOn p {t | (t : ℝ≥0∞) ≤ L}) (hdr : IsDrivenCurve (canonCurve X x₀ p L))
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g (Mo.hullChart (fillH X) 0).2.1 H) {C : ℝ}
    (hC : ∀ q : ℂ, 0 ≤ q.im → ‖g q - q‖ ≤ C) (hR : g (x₀ : ℂ) = R) (hreal : ∀ y : ℝ, x₀ < y → (g (y : ℂ)).im = 0)
    (hmono : StrictMonoOn (fun y : ℝ => (g (y : ℂ)).re) (Ici x₀))
    (hFy : ∀ y : ℝ, x₀ < y → y ∉ Fy → (g (y : ℂ)).re ∉ jumps → β.fn y = b (g (y : ℂ)).re)
    (hft : Restart.FCDet.IsFlowType κ (-(Real.pi / 2)) (BoundaryWord.shiftW x₀ β) xL xR ρL ρR)
    (hfree : ∀ x : ℝ, R < x → ∃ r > 0, Disjoint (ball (x : ℂ) r) (fillH X))
    (hend : L ≠ ⊤ → ∃ x : ℝ, p L.toNNReal = x ∧ x ∈ origBadR κ b R)
    (hcap : L = ⊤ → capLife (canonCurve X x₀ p L) = ⊤) (hfin : capLife (canonCurve X x₀ p L) ≠ ⊤) :
    ∃ y : ℝ, 0 < y ∧ Tendsto (capTrace (canonCurve X x₀ p L)) (𝓝[<] (capLife (canonCurve X x₀ p L)).toNNReal)
      (𝓝 (y : ℂ)) ∧ Vq.IsBadPoint xL xR ρL ρR (y : ℂ) := by
  have hLt : L ≠ ⊤ := fun h => hfin (hcap h)
  obtain ⟨x, hpx, hxb⟩ := hend hLt
  obtain ⟨v, hv, hgv⟩ := exists_preimage_right hgc hR hreal hC hxb.1
  have huniq : ∀ z : ℂ, 0 ≤ z.im → g z = p L.toNNReal → z = v := fun z hz hgz =>
    unique_preimage hA hgc hgi hR hmono hC hfree hxb.1 hv hgv hz (hgz.trans hpx)
  have hz := tendsto_canonCurve_atTop hA hL0 hLt hpc hdr hgc hgi hC huniq
  have hz' := Lk.tendsto_capTrace_left hdr hfin hz
  refine ⟨v - x₀, by linarith, by simpa using hz', ?_⟩
  exact rel_bad_of_phys hκ hb hgc hmono hFy hft (by linarith) (by rw [sub_add_cancel]; exact hgv) hxb

/-- A point off the closed bad set of the cell has a positive cell gauge. -/
theorem cellGauge_pos {Ω : Type*} {κ' ψ : ℝ} {cw : Ω → Restart.BoundaryWord} {w : WordType} {ω : Ω} {z : ℂ}
    (hz : z ∉ closure (badSet (cellXL κ' ψ cw w ω) (cellXR κ' ψ cw w ω) (typedRhoL w) (typedRhoR w))) :
    0 < cellGauge κ' ψ cw w ω z :=
  lt_min (infEDist_pos_iff_notMem_closure.2 (by rwa [closure_closure])) one_pos

/-- **F2b′'s relative facts at one sample.** -/
theorem relFactsAt_of {Ω : Type*} (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hA : IsHPHull (fillH X)) (hL0 : L ≠ 0) (hpc : ContinuousOn p {t | (t : ℝ≥0∞) ≤ L})
    (hdr : IsDrivenCurve (canonCurve X x₀ p L)) (hgc : ContinuousOn g {z | 0 ≤ z.im})
    (hgi : EqOn g (Mo.hullChart (fillH X) 0).2.1 H) {C : ℝ} (hC : ∀ q : ℂ, 0 ≤ q.im → ‖g q - q‖ ≤ C)
    (hR : g (x₀ : ℂ) = R) (hreal : ∀ y : ℝ, x₀ < y → (g (y : ℂ)).im = 0)
    (hmono : StrictMonoOn (fun y : ℝ => (g (y : ℂ)).re) (Ici x₀))
    (hFy : ∀ y : ℝ, x₀ < y → y ∉ Fy → (g (y : ℂ)).re ∉ jumps → β.fn y = b (g (y : ℂ)).re)
    (hleft : ∀ y : ℝ, y < x₀ → y ∉ β.jumps → -2 < Sec4.cumWeightLeft κ (β.fn y + -(Real.pi / 2) * chiC κ))
    (hfree : ∀ x : ℝ, R < x → ∃ r > 0, Disjoint (ball (x : ℂ) r) (fillH X))
    (hRnot : R ∉ closure (origBadR κ b R))
    (hav : ∀ t : ℝ≥0, (t : ℝ≥0∞) < L → ∀ x : ℝ, p t = x → R < x → x ∉ closure (origBadR κ b R))
    (hend : L ≠ ⊤ → ∃ x : ℝ, p L.toNNReal = x ∧ x ∈ origBadR κ b R)
    (hcap : L = ⊤ → capLife (canonCurve X x₀ p L) = ⊤)
    {cw : Ω → Restart.BoundaryWord} {types : Set WordType} {ω : Ω}
    (hcwω : cw ω = BoundaryWord.shiftW x₀ β)
    (htype : angleWordType κ (-(Real.pi / 2)) (cw ω) ∈ types) :
    RelFactsAt κ (-(Real.pi / 2)) cw types (canonCurve X x₀ p L) ω := by
  set ψ : ℝ := -(Real.pi / 2) with hψ
  set w : WordType := angleWordType κ ψ (cw ω) with hwdef
  have hcell : ω ∈ wordTypeCell κ ψ cw univ w := ⟨trivial, rfl⟩
  have hft0 := Restart.FCDet.isFlowType_of_mem_typeSet (mem_typeSet_of_mem_wordTypeCell hcell)
  have hft : Restart.FCDet.IsFlowType κ ψ (BoundaryWord.shiftW x₀ β) (cellXL κ ψ cw w ω) (cellXR κ ψ cw w ω)
      (typedRhoL w) (typedRhoR w) := by
    rw [← hcwω]; exact hft0
  have hrel : ∀ z, relGauge κ ψ cw types ω z = cellGauge κ ψ cw w ω z := fun z =>
    relGauge_eq κ ψ cw types htype rfl z
  have hcl_le : closure (origBadR κ b R) ⊆ Ici R := closure_minimal (fun y hy => le_of_lt hy.1) isClosed_Ici
  -- a relative point read back off the closure is off the relative closed bad set
  have hoff : ∀ z : ℂ, (∀ x : ℝ, g (z + x₀) = x → x ∉ closure (origBadR κ b R)) →
      0 < relGauge κ ψ cw types ω z := fun z hz => by
    rw [hrel]
    refine cellGauge_pos fun hmem => ?_
    obtain ⟨x, hx, hxcl⟩ := readback_closure hκ hb hgc hR hreal hmono hFy hleft hft hmem
    exact hz x hx hxcl
  refine ⟨htype, ?_, ?_, ?_⟩
  · refine hoff 0 fun x hx hxcl => ?_
    rw [zero_add, hR] at hx
    have : R = x := by exact_mod_cast hx
    exact hRnot (this ▸ hxcl)
  · intro s hs
    refine hoff _ fun x hx hxcl => ?_
    have hu := capInv_nonneg (canonCurve X x₀ p L) s
    have hg := g_canonCurve_eq hA hL0 hpc hdr hgc hgi hu
    have hcap' : capTrace (canonCurve X x₀ p L) s = canonCurve X x₀ p L (capInv (canonCurve X x₀ p L) s) := rfl
    rw [hcap', hg] at hx
    have ht : ((Nc.cTime L (capInv (canonCurve X x₀ p L) s) : ℝ≥0) : ℝ≥0∞) < L := by
      by_cases hLt : L = ⊤
      · rw [hLt]; exact ENNReal.coe_lt_top
      · exact cTime_lt hLt hL0 hu
    rcases (show R ≤ x from hcl_le hxcl).lt_or_eq with hlt | heq
    · exact hav _ ht x hx hlt hxcl
    · exact hRnot (heq ▸ hxcl)
  · intro hfin
    obtain ⟨y, -, hy, hbad⟩ := endpoint_bad hκ hb hA hL0 hpc hdr hgc hgi hC hR hreal hmono hFy hft hfree hend
      hcap hfin
    have hcont : Continuous fun z => relGauge κ ψ cw types ω z := continuous_relGauge κ ψ cw types ω
    have h0 : relGauge κ ψ cw types ω (y : ℂ) = 0 := by
      rw [hrel]
      unfold cellGauge
      rw [infEDist_zero_of_mem (subset_closure (show (y : ℂ) ∈ badSet (cellXL κ ψ cw w ω) (cellXR κ ψ cw w ω)
        (typedRhoL w) (typedRhoR w) from hbad)), zero_min]
    have h1 := (hcont.tendsto (y : ℂ)).comp hy
    rw [h0] at h1
    have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
    exact h2

end Facts

end InteractingSLE.Theorem14.SB.Ne

/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2UbExt
import InteractingSLE.Spec.Sec7.ContinuityProb10Seed
import InteractingSLE.Spec.Supplement.G12Low
import InteractingSLE.Spec.Exist.DetField

/-!
# A far right mark is swallowed on an infinite lifetime (the target change, then Lemma G12)

Packet PROVE-GW2-RELDET (round 38, decision D73 route (ii)). The tip exclusion of the stopped stage law reads, in the
relative stage chart (the counterflow tip at `∞`, the flow line's target), as: the stage flow line does not reach its
target `∞` without first meeting the far right boundary ray, i.e. without swallowing the far right mark. Lemma G12
avoids non-target boundary points only, so the target is moved first.

For an integrated `SLE_κ(ρ)` evolution of a distinct word whose right list has length `j + 1 + m` (`j ≥ 1`), retarget at
the right mark `x_j` (`Zhan.Retarget.exists_retarget_evolution_of_seed_stop`, LP9's transformed word). The old target
`∞` becomes the left mark `−1` of weight `κ − 6 − S` (`S` the total weight), so the left cumulative weight through `−1`
is `κ − 6 − Σ ρ_R` (`sum_filter_retargetρL`). If `Σ ρ_R < κ/2 − 2` this is `> κ/2 − 4`, and Lemma G12
(`Supp7.G12Low.ae_trace_ne_left_of_exists`, the original left marks lie in `(−1, 0]`) says the retargeted trace never
visits `−1`. The local retargeted evolution is extended to an integrated one (`exists_extension_of_stop`), whose
trace is given by Theorem 1.3.

On the other hand, on an infinite lifetime without swallowing `x_j` there is no separation (`sepTime = ⊤`), and the
pulled-back trace is the original one: a bounded original trace would give bounded hulls of capacity `2t → ∞`, so the
new horizon is finite and the retargeted trace ends at the pole `−1` (`newTrace_eq_neg_one_of_noSep`, the argument of
`Zhan.Retarget.PullData.isGeneratingTrace_top`).

* **`sum_filter_retargetρL`**: the left cumulative weight through `−1` of LP9's word;
* **`newTrace_eq_neg_one_of_noSep`** (pathwise);
* **`ae_exists_swallow_of_top`**: almost surely, on an infinite lifetime the far mark `x_j` is swallowed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open Sec2 Sec2.Assembly Sec2.Assembly2 Sec2.Assembly3 Sec7 LocalExt Zhan.Retarget

/-! ### The weight through the old target -/

/-- **The left cumulative weight of LP9's word through the old target `−1`** is `κ − 6 − Σ ρ_R`: the original left
marks (in `(−1, 0]`, weights `ρ_L`) and the old target (weight `κ − 6 − (Σ ρ_L + Σ ρ_R)`); the later right marks lie
below `−1`. -/
theorem sum_filter_retargetρL {κ : ℝ} {nL j m : ℕ} {xL : Fin nL → ℝ} {xR : Fin (j + 1 + m) → ℝ}
    (ρL : Fin nL → ℝ) (ρR : Fin (j + 1 + m) → ℝ) (hD : LP.IsDistinctForceWord xL xR) (hj : 1 ≤ j) :
    ∑ i ∈ Finset.univ.filter (fun i => (-1 : ℝ) ≤ LP.retargetXL xL xR i), LP.retargetρL κ ρL ρR i =
      κ - 6 - ∑ i, ρR i := by
  obtain ⟨⟨-, hL0, -, hR0⟩, -, hmono⟩ := hD
  have hp := LP.retargetPos_pos hmono hR0 hj
  have hψL : ∀ i, -1 < Sec7.targetChangeReal (LP.retargetPos xR) (xL i) := fun i =>
    Sec7.neg_one_lt_targetChangeReal hp (lt_of_le_of_lt (hL0 i) hp)
  have hlater : ∀ l : Fin m, Sec7.targetChangeReal (LP.retargetPos xR) (xR (Fin.natAdd (j + 1) l.rev)) < -1 :=
    fun l => Sec7.targetChangeReal_lt_neg_one hp (LP.retargetPos_lt_xR_natAdd hmono _)
  rw [Finset.sum_filter, Fin.sum_univ_add, Fin.sum_univ_succ]
  simp only [LP.retargetXL, LP.retargetρL, Fin.append_left, Fin.append_right, Fin.cons_zero, Fin.cons_succ]
  have h1 : ∀ i : Fin nL, (if (-1 : ℝ) ≤ Sec7.targetChangeReal (LP.retargetPos xR) (xL i) then ρL i else 0) =
      ρL i := fun i => by simp only [(hψL i).le, ↓reduceIte]
  have h2 : ∀ l : Fin m, (if (-1 : ℝ) ≤ Sec7.targetChangeReal (LP.retargetPos xR) (xR (Fin.natAdd (j + 1) l.rev))
      then ρR (Fin.natAdd (j + 1) l.rev) else 0) = 0 := fun l => by simp only [not_le.2 (hlater l), ↓reduceIte]
  simp only [h1, h2, le_refl, ↓reduceIte, Finset.sum_const_zero, add_zero]
  ring

/-! ### No separation on an infinite lifetime: the retargeted trace ends at `−1` -/

/-- Without a meeting of the driver and the mark, the separation time of an infinite lifetime is infinite. -/
theorem sepTime_top_of_forall_lt {w vk : ℝ≥0 → ℝ} (h : ∀ t, w t < vk t) : sepTime w vk ⊤ = ⊤ :=
  le_antisymm le_top (le_min le_rfl (le_iInf₂ fun s hs => absurd hs.2 (not_le.2 (h s))))

/-- **On an infinite lifetime without separation the retargeted trace ends at the pole `−1`** (pathwise; the argument
of `Zhan.Retarget.PullData.isGeneratingTrace_top`): the new horizon is finite and the retargeted trace is `−1` there.
-/
theorem newTrace_eq_neg_one_of_noSep {κ : ℝ} {nL j m : ℕ} {xL : Fin nL → ℝ} {xR : Fin (j + 1 + m) → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin (j + 1 + m) → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ}
    {vR : Fin (j + 1 + m) → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ⊤)
    (hD : LP.IsDistinctForceWord xL xR) (hj : 1 ≤ j) (hns : ∀ t : ℝ≥0, w t < vR (LP.retargetIdx j m) t)
    {η' : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace (newW xR w vR) (newHorizon (LP.retargetPos xR) w (vR (LP.retargetIdx j m)) ⊤) η')
    (htr : newHorizon (LP.retargetPos xR) w (vR (LP.retargetIdx j m)) ⊤ = ⊤ →
      Tendsto (fun t => ‖η' t‖) atTop atTop) :
    ∃ ρs : ℝ≥0, (ρs : ℝ≥0∞) = newHorizon (LP.retargetPos xR) w (vR (LP.retargetIdx j m)) ⊤ ∧ η' ρs = -1 := by
  have hrd := retargetData_of_isSLEPathUpTo (hp.isSLEPathUpTo le_rfl) hD hj fun t _ => hns t
  set xk := LP.retargetPos xR with hxkdef
  set vk := vR (LP.retargetIdx j m) with hvkdef
  have hd : PullData w vk xk ⊤ := ⟨hrd.pos, hp.1, hrd.sep, hrd.target⟩
  have hη2 : IsGeneratingTrace (newDrv xk w vk) (newHorizon xk w vk ⊤) η' := hη
  have hxk := hd.pos
  -- a uniform distance from `−1` along the whole new time range gives a bounded trace
  have hbdd : ∀ c > 0, (∀ t : ℝ≥0, c ≤ ‖η' (clk (rate xk w vk) t).toNNReal + 1‖) → False := fun c hc h =>
    hd.not_bounded_top hη2 (B := xk * (1 + 1 / c)) fun t => norm_targetChangeInv_le hxk hc (h t)
  by_cases hTn : newHorizon xk w vk ⊤ = ⊤
  · -- impossible
    exfalso
    have htr' := htr hTn
    obtain ⟨ρ₀, hρ₀⟩ := (tendsto_atTop.1 htr') 2 |>.exists_forall_of_atTop
    have hcont : ContinuousOn η' (Icc 0 ρ₀) := hη2.2.1.mono fun ρ _ =>
      show (ρ : ℝ≥0∞) ≤ newHorizon xk w vk ⊤ by rw [hTn]; exact le_top
    obtain ⟨c, hc, hcle⟩ := exists_pos_le_norm_add_one hcont fun ρ _ =>
      hd.ne_neg_one_of_lt hη2 (by rw [hTn]; exact ENNReal.coe_lt_top)
    refine hbdd (min c 1) (lt_min hc one_pos) fun t => ?_
    set ρ := (clk (rate xk w vk) t).toNNReal
    rcases le_total ρ ρ₀ with hρ | hρ
    · exact (min_le_left _ _).trans (hcle ρ ⟨zero_le, hρ⟩)
    · have h2 := hρ₀ ρ hρ
      have : (1 : ℝ) ≤ ‖η' ρ + 1‖ := by
        have := norm_sub_norm_le (η' ρ) (-1)
        rw [norm_neg, norm_one, sub_neg_eq_add] at this
        linarith
      exact (min_le_right _ _).trans this
  -- a finite new horizon
  set ρs := (newHorizon xk w vk ⊤).toNNReal with hρs
  have hρs' : (ρs : ℝ≥0∞) = newHorizon xk w vk ⊤ := ENNReal.coe_toNNReal hTn
  have hcont : ContinuousOn η' (Icc 0 ρs) := hη2.2.1.mono fun ρ hρ => by rw [← hρs']; exact_mod_cast hρ.2
  have hle : ∀ t : ℝ≥0, (clk (rate xk w vk) t).toNNReal ≤ ρs := fun t => by
    have := (hd.clk_lt (t := t) ENNReal.coe_lt_top).le
    rw [← hρs'] at this
    exact_mod_cast this
  refine ⟨ρs, hρs', ?_⟩
  by_contra hne
  obtain ⟨c, hc, hcle⟩ := exists_pos_le_norm_add_one hcont fun ρ hρ => by
    rcases hρ.2.lt_or_eq with hlt | heq
    · exact hd.ne_neg_one_of_lt hη2 (by rw [← hρs']; exact_mod_cast hlt)
    · rw [heq]; exact hne
  exact hbdd c hc fun t => hcle _ ⟨zero_le, hle t⟩

/-! ### The far mark is swallowed on an infinite lifetime -/

open Classical in
/-- **A far right mark is swallowed on an infinite lifetime** (`0 < κ < 4`; Theorem 1.3 as input, for the trace of the
retargeted evolution). For an integrated evolution of a distinct word with a left mark and a right list of length
`j + 1 + m` (`j ≥ 1`) whose total right weight is `< κ/2 − 2`, almost surely, if the lifetime is infinite, the driver
meets the right mark `x_j` at some time. -/
theorem ae_exists_swallow_of_top (h13 : Exist.Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {nL j m : ℕ} {xL : Fin nL → ℝ} {xR : Fin (j + 1 + m) → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin (j + 1 + m) → ℝ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin (j + 1 + m) → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (hD : LP.IsDistinctForceWord xL xR) (hj : 1 ≤ j) (hnL : 0 < nL)
    (hS : ∑ i, ρR i < κ / 2 - 2) (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ → ∃ t : ℝ≥0, VR (LP.retargetIdx j m) t ω ≤ W t ω := by
  by_cases hthr : ForceWord.ThresholdCondition ρL ρR 0 xL xR
  · -- an inadmissible seed: the lifetime is `0`
    filter_upwards [hE.2.2.2.2] with ω hp hζ
    exfalso
    have hpos : ((0 : ℝ≥0) : ℝ≥0∞) < ζ ω := by rw [hζ]; exact ENNReal.coe_lt_top
    have hu := hp.isSLEPathUpTo le_rfl
    have h := hu.not_threshold hpos
    have e1 : (fun i => VL i 0 ω) = xL := funext hu.vL_zero
    have e2 : (fun i => VR i 0 ω) = xR := funext hu.vR_zero
    have e0 : W 0 ω = 0 := hu.w_zero
    simp only [e0] at h
    rw [e1, e2] at h
    exact h hthr
  -- the retargeted local evolution and its first positive localizing time
  obtain ⟨𝓘, β, τ, -, hτ, hloc, S, hSst, hSae⟩ := exists_retarget_evolution_of_seed_stop hκ hD hj hE hthr
  have hF := (LP.isDistinctForceWord_retarget hD hj).1
  have hTst : IsStoppingTime (usualAugmentation 𝓘 (P.prod P))
      fun p : Ω × Ω => (firstPos (fun n (q : Ω × Ω) => S n q.1) p : WithTop ℝ≥0) :=
    fun t => Ito.le_usualAugmentation 𝓘 (P.prod P) t _ (isStoppingTime_firstPos hSst t)
  have hT0 : ∀ p : Ω × Ω, 0 < firstPos (fun n (q : Ω × Ω) => S n q.1) p := fun p => firstPos_pos _ p
  have hTτ : ∀ᵐ p ∂(P.prod P), (firstPos (fun n (q : Ω × Ω) => S n q.1) p : ℝ≥0∞) < τ p.1 := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := P) (ν := P)).ae hSae] with p hp
    exact firstPos_lt (S := fun n (q : Ω × Ω) => S n q.1) (τ := fun q => τ q.1) hp.1 hp.2
  have hgood : ∀ᵐ p ∂(P.prod P), GoodWord (LP.retargetρL κ ρL ρR) (LP.retargetρR ρR)
      (contWord (fun u p => newW xR (fun t => W t p.1) (fun i t => VR i t p.1) u)
        (fun i u p => newVL xR (fun t => W t p.1) (fun i t => VL i t p.1) (fun i t => VR i t p.1) i u)
        (fun i u p => newVR xR (fun t => W t p.1) (fun i t => VR i t p.1) i u)
        (firstPos (fun n (q : Ω × Ω) => S n q.1)) p) := by
    filter_upwards [hloc.ae_path, hTτ] with p hp hpτ
    exact goodWord_of_isSLEPathUpTo hp hF (hT0 p) hpτ
  -- the extension to an integrated evolution of LP9's word, its trace, and Lemma G12 at `−1`
  obtain ⟨𝓖, W₁, VL₁, VR₁, B₁, ζ₁, hG, hag⟩ := exists_extension_of_stop hκ hloc hTst hT0 hTτ hgood
  have h13G := h13 hκ hF hG
  set ηG : Ω × Ω → ℝ≥0 → ℂ := fun p => if h : ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W₁ t p) (ζ₁ p) η ∧
      (ζ₁ p = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop) then h.choose else fun _ => 0 with hηGdef
  have hηG : ∀ᵐ p ∂(P.prod P), IsGeneratingTrace (fun t => W₁ t p) (ζ₁ p) (ηG p) ∧
      (ζ₁ p = ⊤ → Tendsto (fun t => ‖ηG p t‖) atTop atTop) := by
    filter_upwards [h13G] with p hp
    have hex := hp.2
    simp only [hηGdef, hex, ↓reduceDIte]
    exact hex.choose_spec
  have hpos := LP.retargetPos_pos hD.2.2 hD.1.2.2.2 hj
  have hex : ∃ i, (-1 : ℝ) < LP.retargetXL xL xR i := ⟨Fin.castAdd (m + 1) ⟨0, hnL⟩, by
    simp only [LP.retargetXL, Fin.append_left]
    exact Sec7.neg_one_lt_targetChangeReal hpos (lt_of_le_of_lt (hD.1.2.1 _) hpos)⟩
  have hSw : κ / 2 - 4 < ∑ i ∈ Finset.univ.filter (fun i => (-1 : ℝ) ≤ LP.retargetXL xL xR i),
      LP.retargetρL κ ρL ρR i := by
    rw [sum_filter_retargetρL ρL ρR hD hj]
    linarith
  have hG12 := Supp7.G12Low.ae_trace_ne_left_of_exists hκ hκ4 hF hG (hηG.mono fun p hp => hp.1)
    (by norm_num : (-1 : ℝ) < 0) hex hSw
  -- on the bad event the retargeted trace ends at `−1`
  have hpath := (Measure.quasiMeasurePreserving_fst (μ := P) (ν := P)).ae hE.2.2.2.2
  have hτ' := (Measure.quasiMeasurePreserving_fst (μ := P) (ν := P)).ae hτ
  refine ae_of_ae_prod_fst (Φ := fun ω => ζ ω = ⊤ → ∃ t : ℝ≥0, VR (LP.retargetIdx j m) t ω ≤ W t ω) ?_
  filter_upwards [hG12, hηG, hag, hpath, hτ'] with p hp12 hpη hpag hpp hpτ hζ
  by_contra hns
  simp only [not_exists, not_le] at hns
  rw [hζ] at hpp
  have hsep := sepTime_top_of_forall_lt hns
  have hτp : τ p.1 = newHorizon (LP.retargetPos xR) (fun t => W t p.1) (fun t => VR (LP.retargetIdx j m) t p.1) ⊤ := by
    rw [hpτ, hζ, hsep]
  have hη' : IsGeneratingTrace (newW xR (fun t => W t p.1) (fun i t => VR i t p.1)) (τ p.1) (ηG p) :=
    IsGeneratingTrace.congr_lt (hpη.1.mono_horizon hpag.1) hpag.2
  rw [hτp] at hη'
  have htr : newHorizon (LP.retargetPos xR) (fun t => W t p.1) (fun t => VR (LP.retargetIdx j m) t p.1) ⊤ = ⊤ →
      Tendsto (fun t => ‖ηG p t‖) atTop atTop := fun h =>
    hpη.2 (top_le_iff.1 (h ▸ hτp ▸ hpag.1))
  obtain ⟨ρs, hρs, hend⟩ := newTrace_eq_neg_one_of_noSep hpp hD hj hns hη' htr
  have hle : (ρs : ℝ≥0∞) ≤ ζ₁ p := by
    rw [hρs, ← hτp]
    exact hpag.1
  exact hp12 ρs hle (by rw [hend]; push_cast; ring)

end InteractingSLE.Theorem14.GW2Rd

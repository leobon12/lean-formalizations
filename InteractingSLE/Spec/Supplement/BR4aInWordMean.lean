/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BR4aInWordStep

/-!
# BR4a's relative words: the coupling-mean identity at one original time (deterministic)

Packet PROVE-T14-BR4A3 (`BR4aChain.BR4aWordDetStatement`, conjunct (3); supplement p. 610, (BR4a.1)). Under the
conjugation data `ConjData` at `(t, q)`, the coupling mean of the relative chain with the word of the transformed
field, read at `mob v z`, is the coupling mean of the original chain at `z` plus `χ · lift(z)`
(**`ConjData.mean_eq`**). It is HULLDET's `couplingMean_mob_eq` with the boundary step identity (★)
(`ConjData.step_eq`) and one boundary limit (`ConjData.exists_tendsto_mean`): at the image of an alive real point
`y` both means tend to the flowed words, `b'(y)` and `c(mob v y)`, and the lift to `liftBdry v y`; these cancel by
`word_eq`.

* `flowExt`, `isBHE_flowExt`, `flowJumps_finite`, `flowData_flowVal`;
* **`ConjData.exists_tendsto_mean`**, **`ConjData.mean_eq`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open QuantumZipper (H fwdHull fwdMap logDerivFwd chiC)
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.BR4aIn

open BR4aPath BR4aChain ConformalImage ConformalImageFull Supp8.HullDetGen Sec5.CrossRestart MartChar.RealFlow

/-- The bounded harmonic extension of the flowed force datum of a flow-line word (the coupling-mean extension). -/
def flowExt (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) (w : ℝ → ℝ) (t : ℝ) : ℂ → ℝ :=
  LocalExt.bheAt κ (flowLineRhoL κ b J 0 0) (flowLineRhoR κ b J 0 0)
    (fun i => -rightImg (fun s => -w s) (-flowLineXL b J 0 i) t - w t)
    (fun j => rightImg w (flowLineXR b J 0 j) t - w t)

theorem isBHE_flowExt (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) (w : ℝ → ℝ) (t : ℝ) :
    IsBoundedHarmonicExtension (flowData κ b J w t) (flowJumps b J w t) (flowExt κ b J w t) :=
  LocalExt.isBoundedHarmonicExtension_bheAt _ _ _ _ _

theorem flowJumps_finite (b : ℝ → ℝ) (J : Finset ℝ) (w : ℝ → ℝ) (t : ℝ) : (flowJumps b J w t).Finite :=
  ((Set.finite_range _).union (Set.finite_range _)).insert 0

/-- **The flowed force datum at the image of a real point off the closed hull** is the boundary datum. -/
theorem flowData_flowVal {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J)
    {w : ℝ → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {t : ℝ} (ht : 0 ≤ t) {y : ℝ}
    (hc : (y : ℂ) ∉ closure (fwdHull w t)) (hy0 : y ≠ 0) (hyJ : y ∉ J)
    (hS : flowVal w t y - w t ∉ flowJumps b J w t) : flowData κ b J w t (flowVal w t y - w t) = b y := by
  rcases (flowVal_spec hw hw0 ht hc hy0).2 with ⟨hp, hal, hf⟩ | ⟨hn, hal, hf⟩
  · rw [hf]
    exact fbd_flow_right hκ hb hw ht hp hal hyJ
  · have hne : ∀ i, -gImg (fun s => -w s) (-y) t - w t ≠
        -rightImg (fun s => -w s) (-flowLineXL b J 0 i) t - w t := by
      intro i he
      apply hS
      rw [hf, he]
      exact Set.mem_insert_of_mem _ (Or.inl ⟨i, rfl⟩)
    have h1 := fbd_flow_left hκ hb hw ht (neg_pos.2 hn) hal (by rwa [neg_neg]) hne
    rw [neg_neg] at h1
    rw [hf]
    exact h1

namespace ConjData

variable {w u : ℝ → ℝ} {t q v α κN P : ℝ}

/-- **One boundary limit of the mean difference** at the image of an alive real point. -/
theorem exists_tendsto_mean (h : ConjData w u t q v α κN P) {κ : ℝ} (hκ : 0 < κ) {b' : ℝ → ℝ} {J' : Finset ℝ}
    (hb' : IsPiecewiseConstantBoundaryData b' J') {c : Restart.BoundaryWord}
    (h0 : ∀ u₀ uc : ℂ → ℝ, IsBoundedHarmonicExtension b' J' u₀ → IsBoundedHarmonicExtension c.fn c.jumps uc →
      ∀ z ∈ H, uc z = u₀ (mobInv v z) + chiC κ * (brChart v).2.2 (mobInv v z)) :
    ∃ y₀ : ℂ, (𝓝[H \ fwdHull w t] y₀).NeBot ∧
      Tendsto (fun z => couplingMean κ (fun s => u s) q (flowExt κ c.fn c.jumps u q) (mob v z) -
          couplingMean κ (fun s => w s) t (flowExt κ b' J' w t) z - chiC κ * (brChart v).2.2 z)
        (𝓝[H \ fwdHull w t] y₀) (𝓝 0) := by
  -- a good image point `x > R₀`
  set B : Set ℝ := ((fun X => X + w t) '' flowJumps b' J' w t) ∪
    ((fun x => α - κN / (x - P) - u q) ⁻¹' flowJumps c.fn c.jumps u q) ∪
    (flowVal w t '' ↑(badPts v J' c)) ∪ {P} with hB
  have hBf : B.Finite :=
    ((((flowJumps_finite b' J' w t).image _).union
      ((flowJumps_finite c.fn c.jumps u q).preimage (injective_nfR h.hκN _).injOn)).union
      ((badPts v J' c).finite_toSet.image _)).union (Set.finite_singleton _)
  obtain ⟨x, hxI, hxB⟩ := ((Set.Ioo_infinite (show rightImg w 0 t < rightImg w 0 t + 1 by linarith)).sdiff
    hBf).nonempty
  have hxS : x - w t ∉ flowJumps b' J' w t := fun hm => hxB (Or.inl (Or.inl (Or.inl ⟨_, hm, by ring⟩)))
  have hxS' : α - κN / (x - P) - u q ∉ flowJumps c.fn c.jumps u q := fun hm => hxB (Or.inl (Or.inl (Or.inr hm)))
  -- its alive preimage
  obtain ⟨y, hy0, hal, hg⟩ := Restart.FCAux79.exists_alive_gImg_eq h.hw h.ht (M := x) hxI.1
  have hc := notMem_closure_of_alive h.hw h.hw0 h.ht hal
  have hfv : flowVal w t y = x := by
    rcases (flowVal_spec h.hw h.hw0 h.ht hc hy0.ne').2 with ⟨-, -, hf⟩ | ⟨hn, -, -⟩
    · rw [hf, hg]
    · linarith
  have hyb : y ∉ badPts v J' c := fun hm => hxB (Or.inl (Or.inr ⟨y, hm, hfv⟩))
  obtain ⟨hyJ, -, hyp, hmyJ⟩ := notMem_jumps_of_notMem_badPts h.hv hyb
  obtain ⟨hmc, hm0, hfl⟩ := flowVal_conj h.hw h.hw0 h.hu h.hu0 h.ht h.hq h.hK h.hconj hc hy0.ne' hyp
    (h.flowVal_ne_P hc hy0.ne' hyp)
  rw [hfv] at hfl
  set my : ℝ := y / (v * y + 1) with hmydef
  -- the filter
  have hmemH : H \ fwdHull w t ∈ 𝓝[H] (y : ℂ) := by
    filter_upwards [nhdsWithin_le_nhds (isClosed_closure.isOpen_compl.mem_nhds hc), self_mem_nhdsWithin]
      with z hz hzH
    exact ⟨hzH, fun hzK => hz (subset_closure hzK)⟩
  have hle : 𝓝[H \ fwdHull w t] (y : ℂ) ≤ 𝓝[H] (y : ℂ) := nhdsWithin_mono _ sdiff_subset
  have hge : 𝓝[H] (y : ℂ) ≤ 𝓝[H \ fwdHull w t] (y : ℂ) := nhdsWithin_le_of_mem hmemH
  have hNe : (𝓝[H \ fwdHull w t] (y : ℂ)).NeBot := (neBot_nhdsWithin_H y).mono hge
  refine ⟨y, hNe, ?_⟩
  -- the original mean
  obtain ⟨f, hf⟩ := Supp8.BHMean.exists_isForwardSol_of_notMem_closure h.hw h.hw0 h.ht hc hy0.ne'
  have hfr : (f t).im = 0 := InteractingSLE.im_eq_zero_of_isForwardSol_real h.hw hf ⟨h.ht, le_rfl⟩
  have hfv' : f t = ((x - w t : ℝ) : ℂ) := by
    have := flowVal_eq_of_isForwardSol h.hw h.ht hf hfr
    rw [hfv] at this
    push_cast
    linear_combination this
  have hF1 : Tendsto (fwdMap w t) (𝓝[H \ fwdHull w t] (y : ℂ)) (𝓝[H] ((x - w t : ℝ) : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall
      fun z hz => QuantumZipper.FwdHolo.mapsTo_fwdMap h.hw h.ht hz⟩
    rw [← hfv']
    exact (QuantumZipper.RS.tendsto_fwdMap_of_sol h.hw h.ht hf).mono_left hle
  have hO : Tendsto (fun z => couplingMean κ (fun s => w s) t (flowExt κ b' J' w t) z)
      (𝓝[H \ fwdHull w t] (y : ℂ)) (𝓝 (flowData κ b' J' w t (x - w t) - chiC κ * 0)) :=
    (((isBHE_flowExt κ b' J' w t).2.2 _ hxS).comp hF1).sub
      (((Supp8.BHMean.tendsto_im_logDerivFwd_of_notMem_closure h.hw h.hw0 h.ht hc).mono_left hle).const_mul _)
  -- the relative mean at `mob v z`
  have hmob : Tendsto (mob v) (𝓝[H \ fwdHull w t] (y : ℂ)) (𝓝[H] (my : ℂ)) := by
    rw [hmydef, ← mob_ofReal]
    exact (tendsto_mob_nhdsWithin_H hyp).mono_left hle
  obtain ⟨g, hg'⟩ := Supp8.BHMean.exists_isForwardSol_of_notMem_closure h.hu h.hu0 h.hq hmc hm0
  have hgr : (g q).im = 0 := InteractingSLE.im_eq_zero_of_isForwardSol_real h.hu hg' ⟨h.hq, le_rfl⟩
  have hgv : g q = ((α - κN / (x - P) - u q : ℝ) : ℂ) := by
    have := flowVal_eq_of_isForwardSol h.hu h.hq hg' hgr
    rw [hfl] at this
    push_cast at this ⊢
    linear_combination this
  have hF2 : Tendsto (fun z => fwdMap u q (mob v z)) (𝓝[H \ fwdHull w t] (y : ℂ))
      (𝓝[H] ((α - κN / (x - P) - u q : ℝ) : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall
      fun z hz => QuantumZipper.FwdHolo.mapsTo_fwdMap h.hu h.hq (mob_mem_compl h.hK hz)⟩
    rw [← hgv]
    exact (QuantumZipper.RS.tendsto_fwdMap_of_sol h.hu h.hq hg').comp hmob
  have hRel : Tendsto (fun z => couplingMean κ (fun s => u s) q (flowExt κ c.fn c.jumps u q) (mob v z))
      (𝓝[H \ fwdHull w t] (y : ℂ)) (𝓝 (flowData κ c.fn c.jumps u q (α - κN / (x - P) - u q) - chiC κ * 0)) :=
    (((isBHE_flowExt κ c.fn c.jumps u q).2.2 _ hxS').comp hF2).sub
      (((Supp8.BHMean.tendsto_im_logDerivFwd_of_notMem_closure h.hu h.hu0 h.hq hmc).comp hmob).const_mul _)
  have hLift := ((tendsto_brChart_lift hy0.ne' hyp).mono_left hle).const_mul (chiC κ)
  -- the limit vanishes
  have hv1 : flowData κ b' J' w t (x - w t) = b' y := by
    have := flowData_flowVal hκ hb' h.hw h.hw0 h.ht hc hy0.ne' hyJ (by rwa [hfv])
    rwa [hfv] at this
  have hv2 : flowData κ c.fn c.jumps u q (α - κN / (x - P) - u q) = c.fn my := by
    have := flowData_flowVal hκ c.isPiecewiseConstantBoundaryData h.hu h.hu0 h.hq hmc hm0 hmyJ (by rwa [hfl])
    rwa [hfl] at this
  have hw := word_eq hb' h0 hy0.ne' hyp hyJ hmyJ
  have hfin := (hRel.sub hO).sub hLift
  rw [hv1, hv2, hw] at hfin
  convert hfin using 2
  ring

/-- **The coupling-mean identity at one original time** (BR4a.1): the relative mean with the word of the transformed
field, read at `mob v z`, is the original mean at `z` plus `χ · lift(z)`. -/
theorem mean_eq (h : ConjData w u t q v α κN P) {κ : ℝ} (hκ : 0 < κ) {b' : ℝ → ℝ} {J' : Finset ℝ}
    (hb' : IsPiecewiseConstantBoundaryData b' J') {c : Restart.BoundaryWord}
    (h0 : ∀ u₀ uc : ℂ → ℝ, IsBoundedHarmonicExtension b' J' u₀ → IsBoundedHarmonicExtension c.fn c.jumps uc →
      ∀ z ∈ H, uc z = u₀ (mobInv v z) + chiC κ * (brChart v).2.2 (mobInv v z)) :
    ∀ z ∈ H \ fwdHull w t, couplingMean κ (fun s => u s) q (flowExt κ c.fn c.jumps u q) (mob v z) =
      couplingMean κ (fun s => w s) t (flowExt κ b' J' w t) z + chiC κ * (brChart v).2.2 z := by
  obtain ⟨E, hE, hstep⟩ := h.step_eq hκ hb' h0
  obtain ⟨y₀, hy₀, hlim⟩ := h.exists_tendsto_mean hκ hb' h0
  exact couplingMean_mob_eq h.hw h.hw0 h.hu h.ht h.hq h.hκN h.hK h.hconj (flowJumps_finite b' J' w t)
    (flowJumps_finite c.fn c.jumps u q) (isBHE_flowExt κ b' J' w t) (isBHE_flowExt κ c.fn c.jumps u q) hE _
    hstep hy₀ hlim

end ConjData

end InteractingSLE.Theorem14.BR4aIn

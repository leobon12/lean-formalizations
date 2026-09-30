import QuantumZipper.Proofs.Thm18.ZqCS1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZQ-CORE (12): the sandwich functionals `phiS`, `betaS` and the deterministic sandwich

See `ZqCS1` for the strategy. Own bookkeeping (AGENT_GUIDE cost rule); Sheffield,
arXiv:1012.4797, proof of Prop. 5.5 (p. 65).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function Metric
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace ZqC

open G3Z2b2 D3Plus G1Zm G3Zq G3ZqL G3ZqO Factorization G2PalmLoc G3Cv

/-- The field rebuilt from the pulled-back dyadic coordinates of the zoom of `recF v` at `x`. -/
def Zr (γ L : ℝ) (Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ) (left : Bool) (a : ℝ≥0 → ℝ) (v : ℕ → ℝ)
    (x : ℝ) : FieldSample :=
  reconstruct (g3coordsM γ L Ψ left (recF v, a, 1, x))

/-- The good set at scale `ρ_m`. -/
def okSet (γ L : ℝ) (Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ) (left : Bool) (a : ℝ≥0 → ℝ) (R m : ℕ) :
    Set ((ℕ → ℝ) × ℝ) :=
  {q | mapOK Ψ left a m q.2 ∧
    G3ZqF.dyadCert γ (rhoM m) (dyadData (rhoM m) (Zr γ L Ψ left a q.1 q.2)) ∧
    dyadData (rhoM m) (Zr γ L Ψ left a q.1 q.2) ∉ dyadBad γ (rhoM m) (R + 1)}

/-- The local functional. -/
def phiS (γ L : ℝ) (Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ) (left : Bool) (a : ℝ≥0 → ℝ) (R : ℕ)
    (Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞) (v : ℕ → ℝ) (x : ℝ) : ℝ≥0∞ :=
  ⨆ m : ℕ, (okSet γ L Ψ left a R m).indicator
    (fun q => Γ (dyadT γ (rhoM m) R (dyadData (rhoM m) (Zr γ L Ψ left a q.1 q.2)))) (v, x)

/-- The bad functional. -/
def betaS (γ L : ℝ) (Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ) (left : Bool) (a : ℝ≥0 → ℝ) (R : ℕ)
    (v : ℕ → ℝ) (x : ℝ) : ℝ≥0∞ :=
  (⋃ m, okSet γ L Ψ left a R m)ᶜ.indicator 1 (v, x)

variable {γ : ℝ} {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ}

theorem measurable_Zr (hsel : G1PsiSel γ Ψ) (L : ℝ) (left : Bool) (a : ℝ≥0 → ℝ) :
    Measurable fun q : (ℕ → ℝ) × ℝ => Zr γ L Ψ left a q.1 q.2 := by
  have hp : Measurable fun q : (ℕ → ℝ) × ℝ => ((recF q.1, a, 1, q.2) : G3Par) :=
    (measurable_recF.comp measurable_fst).prodMk (measurable_const.prodMk
      (measurable_const.prodMk measurable_snd))
  have h := measurable_reconstruct.comp ((measurable_g3coordsM hsel L left).comp hp)
  simp only [Function.comp_def] at h
  exact h

theorem measurableSet_okSet (hsel : G1PsiSel γ Ψ) (L : ℝ) (left : Bool) (a : ℝ≥0 → ℝ)
    (R m : ℕ) : MeasurableSet (okSet γ L Ψ left a R m) := by
  have hd : Measurable fun q : (ℕ → ℝ) × ℝ => dyadData (rhoM m) (Zr γ L Ψ left a q.1 q.2) :=
    (measurable_dyadData _).comp (measurable_Zr hsel L left a)
  have e : okSet γ L Ψ left a R m = (Prod.snd ⁻¹' {x | mapOK Ψ left a m x}) ∩
      ((fun q : (ℕ → ℝ) × ℝ => dyadData (rhoM m) (Zr γ L Ψ left a q.1 q.2)) ⁻¹'
        {ξ | G3ZqF.dyadCert γ (rhoM m) ξ} ∩
      (fun q : (ℕ → ℝ) × ℝ => dyadData (rhoM m) (Zr γ L Ψ left a q.1 q.2)) ⁻¹'
        (dyadBad γ (rhoM m) (R + 1))ᶜ) := rfl
  rw [e]
  exact (measurable_snd (measurableSet_mapOK hsel left a m)).inter
    ((hd (G3ZqF.measurableSet_dyadCert γ _)).inter
      (hd (measurableSet_dyadBad γ _ _).compl))

theorem measurable_phiS (hsel : G1PsiSel γ Ψ) (L : ℝ) (left : Bool) (a : ℝ≥0 → ℝ) (R : ℕ)
    {Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞} (hΓ : Measurable Γ) :
    Measurable (uncurry (phiS γ L Ψ left a R Γ)) := by
  have e : uncurry (phiS γ L Ψ left a R Γ) = fun q => ⨆ m : ℕ, (okSet γ L Ψ left a R m).indicator
      (fun q => Γ (dyadT γ (rhoM m) R (dyadData (rhoM m) (Zr γ L Ψ left a q.1 q.2)))) q := by
    funext q; rfl
  rw [e]
  refine Measurable.iSup fun m => Measurable.indicator ?_ (measurableSet_okSet hsel L left a R m)
  have h := hΓ.comp ((measurable_dyadT γ (rhoM m) R).comp
    ((measurable_dyadData _).comp (measurable_Zr hsel L left a)))
  simp only [Function.comp_def] at h
  exact h

theorem measurable_betaS (hsel : G1PsiSel γ Ψ) (L : ℝ) (left : Bool) (a : ℝ≥0 → ℝ) (R : ℕ) :
    Measurable (uncurry (betaS γ L Ψ left a R)) := by
  have e : uncurry (betaS γ L Ψ left a R) = (⋃ m, okSet γ L Ψ left a R m)ᶜ.indicator 1 := by
    funext q; rfl
  rw [e]
  exact measurable_one.indicator
    (MeasurableSet.iUnion fun m => measurableSet_okSet hsel L left a R m).compl

theorem betaS_le_one (L : ℝ) (left : Bool) (a : ℝ≥0 → ℝ) (R : ℕ) (v : ℕ → ℝ) (x : ℝ) :
    betaS γ L Ψ left a R v x ≤ 1 := indicator_le (fun _ _ => le_rfl) _

theorem dyadicRoundC_dyC (i : DyIdx) : dyadicRoundC i.1 (dyC i) = dyC i := by
  have h2 : (0 : ℝ) < 2 ^ i.1 := by positivity
  apply Complex.ext
  · simp only [dyadicRoundC, dyadicRound, dyC]
    rw [mul_div_cancel₀ _ h2.ne', Int.floor_intCast]
  · simp only [dyadicRoundC, dyadicRound, dyC]
    rw [mul_div_cancel₀ _ h2.ne', Int.floor_intCast]

theorem dyadData_eq_of_agreeNear {r : ℝ} {y y' : FieldSample} (h : AgreeNear y y' r) :
    dyadData r y = dyadData r y' := by
  funext i
  have e := dyadicRoundC_dyC i.1
  have hz : ‖dyadicRoundC i.1.1 (dyC i.1)‖ + radius i.1.2.1 < r := by rw [e]; exact i.2
  have := h i.1.1 i.1.2.1 (dyC i.1) hz
  rw [e] at this
  exact this

/-- `Zr` agrees with the zoom of `recF v` on every dyadic circle. -/
theorem agreeNear_Zr (hsel : G1PsiSel γ Ψ) {a : ℝ≥0 → ℝ} (ha : G3ZqGoodPath γ a) (L : ℝ)
    (left : Bool) (v : ℕ → ℝ) (x r : ℝ) :
    AgreeNear (Zr γ L Ψ left a v x) (zoomFieldVia γ L (recF v) x (mapX Ψ left a x)) r := by
  intro n k z _
  have hc := g3coordsM_eq (p := ((recF v, a, 1, x) : G3Par)) hsel L left ha.1 ha.2
    (zero_lt_one' ℝ)
  obtain ⟨i, hi⟩ := dyadicIndex_surj n k z
  have h := reconstruct_coords_apply (zoomFieldVia γ L (recF v) x (mapX Ψ left a x)) i
  rw [hi] at h
  unfold Zr
  rw [hc]
  exact h

/-- **The deterministic sandwich.** -/
theorem sandwichS (hsel : G1PsiSel γ Ψ) {a : ℝ≥0 → ℝ} (ha : G3ZqGoodPath γ a) {left : Bool}
    {x : ℝ} (hxs : x ∈ g1SideHalf left) (L : ℝ) (R : ℕ)
    (Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞) (hΓ1 : ∀ y, Γ y ≤ 1) (y : FieldSample) :
    Γ (g1zLocData R (g1zM γ L Ψ left ((y, a), x))) ≤
        phiS γ L Ψ left a R Γ (vOf y) x + betaS γ L Ψ left a R (vOf y) x ∧
      phiS γ L Ψ left a R Γ (vOf y) x ≤
        Γ (g1zLocData R (g1zM γ L Ψ left ((y, a), x))) + betaS γ L Ψ left a R (vOf y) x := by
  classical
  set c := Γ (g1zLocData R (g1zM γ L Ψ left ((y, a), x))) with hc
  set Zy := zoomFieldVia γ L y x (mapX Ψ left a x) with hZy
  have hcZ : c = Γ (g1zLocData R (lawOf (canonProxy γ Zy))) := by
    rw [hc, G3ZqF.g1zM_eq_canonProxy hsel ha L left y fz x]
    rfl
  -- on a good scale the term is `c`
  have hkey : ∀ m, (vOf y, x) ∈ okSet γ L Ψ left a R m →
      Γ (dyadT γ (rhoM m) R (dyadData (rhoM m) (Zr γ L Ψ left a (vOf y) x))) = c := by
    intro m hm
    obtain ⟨hmap, hcert, hbad⟩ := hm
    have hψm : Measurable (mapX Ψ left a x) :=
      (g3mapB_props hsel ha.1 ha.2 left (zero_lt_one' ℝ) (x / 1)).2.2
    have hag2 := agreeNear_zoomFieldVia_recF γ L y x hψm (hpsi_of_mapOK hsel ha left hmap)
    have hag : AgreeNear (Zr γ L Ψ left a (vOf y) x) Zy (rhoM m) := fun n k z hz =>
      (agreeNear_Zr hsel ha L left (vOf y) x (rhoM m) n k z hz).trans (hag2 n k z hz)
    have hdd := dyadData_eq_of_agreeNear hag
    rw [hdd] at hcert hbad ⊢
    have hg' := G3ZqF.exists_vague_of_dyadCert hcert
    have hbR : dyadData (rhoM m) Zy ∉ dyadBad γ (rhoM m) R := by
      intro hb
      apply hbad
      simp only [dyadBad, mem_setOf_eq] at hb ⊢
      intro h
      apply hb
      refine ⟨h.1, lt_of_le_of_lt ?_ h.2⟩
      have := h.1.le
      push_cast
      nlinarith
    rw [hcZ, gamma_eq_of_not_bad Γ (fun _ _ _ _ => rfl) hg' hbad,
      locFieldFull_canonicalOn_eq_dyadT_of_good hg' hbR]
  by_cases hex : ∃ m, (vOf y, x) ∈ okSet γ L Ψ left a R m
  · have hβ : betaS γ L Ψ left a R (vOf y) x = 0 := by
      unfold betaS
      rw [indicator_of_notMem (show (vOf y, x) ∉ (⋃ m, okSet γ L Ψ left a R m)ᶜ from
        fun h => h (mem_iUnion.2 hex))]
    have hφ : phiS γ L Ψ left a R Γ (vOf y) x = c := by
      obtain ⟨m₀, hm₀⟩ := hex
      refine le_antisymm (iSup_le fun m => ?_) (le_iSup_of_le m₀ ?_)
      · by_cases hm : (vOf y, x) ∈ okSet γ L Ψ left a R m
        · rw [indicator_of_mem hm]; exact (hkey m hm).le
        · rw [indicator_of_notMem hm]; exact bot_le
      · rw [indicator_of_mem hm₀]; exact (hkey m₀ hm₀).ge
    rw [hβ, hφ, add_zero]
    exact ⟨le_rfl, le_rfl⟩
  · have hβ : betaS γ L Ψ left a R (vOf y) x = 1 := by
      unfold betaS
      rw [indicator_of_mem (show (vOf y, x) ∈ (⋃ m, okSet γ L Ψ left a R m)ᶜ from
        fun h => hex (mem_iUnion.1 h))]; rfl
    have hφ : phiS γ L Ψ left a R Γ (vOf y) x = 0 := by
      refine le_antisymm (iSup_le fun m => ?_) bot_le
      rw [indicator_of_notMem (fun h => hex ⟨m, h⟩)]
    rw [hβ, hφ, zero_add]
    exact ⟨hΓ1 _, bot_le⟩

end ZqC
end Thm18Asm
end QuantumZipper

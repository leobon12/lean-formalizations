import QuantumZipper.Proofs.Zipper.ESMLen

/-!
# LR-ID in the coordinates of E-SM (decision D21)

E-SM-inst (a) restated with the stopping times of E-SM-inst (b): the length integral of LR-ID
(`B5.ae_lr_id_rhs`, level times `tᴸ ℓ` of `lenRHS`) is rewritten with the level times
`T_ℓ = levelTime lenA T ℓ` of `ESM.lintegral_levelTime_strongMarkov_lenA` and the E-SM level
event `{ℓ < lenA T}` (the E-SM-abs event is `{ℓ ≤ lenA T}`; for fixed `ω` the two differ at one
level `ℓ`, a Lebesgue-null set). So parts (a) and (b) of E-SM talk about the same random times, as
the blueprint's `𝐏|_{τ_x ≤ T} = w · 𝐑` requires.

* `ae_lr_id_levelTime`: unconditional (inputs B3(a) and `RohdeSchrammSimple` only).

Sources: Sheffield, arXiv:1012.4797, Lemma 5.6 and its proof (pp. 66–68); bookkeeping own.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace ESM

open LengthMarkov

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

/-- **LR-ID with the E-SM stopping times, a.s.** With `V = Vr κ T B ω`, `T_ℓ = levelTime lenA T ℓ`:
`∫⁻_{[−δ,0]} 1{τ_x < T} G(x, C_x) dν = e^{γ(−m)/2} ∫⁻_{ℓ>0} 1{ℓ < lenA T, −δ ≤ 0₋(T − T_ℓ)}
  G(0₋(T − T_ℓ), zipCapDown γ T_ℓ 𝒵) dℓ`. -/
theorem ae_lr_id_levelTime (hReg : Blueprint.RevCouplingBoundaryMeasureRegular)
    (hRSS : Blueprint.RohdeSchrammSimple) (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T)
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    (ϖ : Measure ℂ) (δ : ℝ) (G : Ω → ℝ → FieldSample × (ℝ → ℝ) → ℝ≥0∞) :
    ∀ᵐ ω ∂P,
      ∫⁻ x in Icc (-δ) 0, {x | realHitTime (B2.Vr κ T B ω) x < ENNReal.ofReal T}.indicator
          (fun x => G ω x (B2.collided κ T B X ω x)) x ∂E1.nuPalm κ T B X ϖ ω =
        ENNReal.ofReal (Real.exp (Real.sqrt κ * -(E1.mReg κ T B X ϖ ω) / 2)) *
          ∫⁻ ℓ in Ioi (0 : ℝ),
            {ℓ | ENNReal.ofReal ℓ < lenA κ T B X T.toNNReal ω ∧
                -δ ≤ zeroMinus (B2.Vr κ T B ω)
                  (T - levelTime (lenA κ T B X) T.toNNReal ℓ.toNNReal ω)}.indicator
              (fun ℓ => G ω (zeroMinus (B2.Vr κ T B ω)
                  (T - levelTime (lenA κ T B X) T.toNNReal ℓ.toNNReal ω))
                (zipCapDown (Real.sqrt κ) (levelTime (lenA κ T B X) T.toNNReal ℓ.toNNReal ω)
                  (B2.cfg κ B X ω))) ℓ := by
  filter_upwards [B5.ae_lr_id_rhs hReg hRSS hκ hκ4 hT hB hX hind ϖ δ G,
    ae_mem_lenGood hReg hRSS hκ hκ4 hT hB hX hind, B5.ae_nu0_regular hReg hκ hκ4 hT hB hX hind,
    B5.ae_zeroMinus_Vr_facts hRSS hκ hκ4.le hT P B hB] with ω hlr hG hν hzf
  obtain ⟨hatom, hpos, hfin⟩ := hν
  obtain ⟨hz0, ha, hanti, -, hhit, -⟩ := hzf
  rw [hlr]
  congr 1
  refine setLIntegral_congr_fun measurableSet_Ioi fun ℓ hℓ => ?_
  have hℓ' : (0 : ℝ) < ℓ := hℓ
  have hcoe : ((ℓ.toNNReal : ℝ≥0) : ℝ) = ℓ := Real.coe_toNNReal _ hℓ'.le
  have hiff := B5.lenTime_mem_Ioo_iff (A := B5.lenRHS κ T B X ω)
    (τ := fun x => (realHitTime (B2.Vr κ T B ω) x).toReal) hatom hpos ha (hfin _ _) hT
    (fun s _ => rfl) hanti rfl hz0 (fun x hx => ⟨(hhit x hx).2.1, (hhit x hx).2.2⟩) hℓ'
  have hAT : lenA κ T B X T.toNNReal ω = qBoundaryMeasure (Real.sqrt κ) (B2.h0f κ T B X ω)
      (Icc (zeroMinus (B2.Vr κ T B ω) T) 0) := by
    rw [lenA_of_mem hG, Real.coe_toNNReal _ hT.le, min_self]
    show qBoundaryMeasure _ _ (Icc _ (zeroMinus (B2.Vr κ T B ω) (T - T))) = _
    rw [sub_self, hz0]
  have hlenA : ENNReal.ofReal ℓ < lenA κ T B X T.toNNReal ω ↔
      ℓ < (qBoundaryMeasure (Real.sqrt κ) (B2.h0f κ T B X ω)
        (Icc (zeroMinus (B2.Vr κ T B ω) T) 0)).toReal := by
    rw [hAT]
    exact ENNReal.ofReal_lt_iff_lt_toReal hℓ'.le (hfin _ _).ne
  simp only [Set.indicator_apply, Set.mem_setOf_eq]
  by_cases h : 0 < ESM.lenTime (B5.lenRHS κ T B X ω) ℓ ∧
      ESM.lenTime (B5.lenRHS κ T B X ω) ℓ < T
  · have heq := levelTime_lenA_eq_lenTime hT.le hG (ℓ := ℓ.toNNReal)
      (by rw [hcoe]; exact h.1) (by rw [hcoe]; exact h.2)
    rw [hcoe] at heq
    rw [heq]
    have hl : ENNReal.ofReal ℓ < lenA κ T B X T.toNNReal ω := hlenA.2 (hiff.1 h)
    by_cases hd : -δ ≤ zeroMinus (B2.Vr κ T B ω) (T - ESM.lenTime (B5.lenRHS κ T B X ω) ℓ)
    · rw [if_pos ⟨h.1, h.2, hd⟩, if_pos ⟨hl, hd⟩]
    · rw [if_neg (fun hm => hd hm.2.2), if_neg (fun hm => hd hm.2)]
  · have hl : ¬ ENNReal.ofReal ℓ < lenA κ T B X T.toNNReal ω :=
      fun hl => h (hiff.2 (hlenA.1 hl))
    rw [if_neg (fun hm => h ⟨hm.1, hm.2.1⟩), if_neg (fun hm => hl hm.1)]

end ESM
end QuantumZipper

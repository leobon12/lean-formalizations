import QuantumZipper.Proofs.Zipper.LocLenPairCfgLeft
import QuantumZipper.Proofs.Zipper.FlowRegAlive

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D75, task R6a: the open-arc capacity cocycle in the `Γ⁰` picture, both sides (no tip input)

`lenPairCocycleCfgArc_holds : LenPairCocycleCfgArcStmt`.

* Left side: `ae_leftCocycleArc` (LocLenPairCfgLeft.lean; fixed chart `T`, Sheffield
  arXiv:1012.4797 p. 56 and p. 70, Berestycki–Powell arXiv:2404.16642 Def 8.12 p. 281).
* Right side: the left side for the reflected `Γ⁰` pair `(−B, X ∘ refl)` (Sheffield §5.4 p. 72,
  "by symmetry"; the route of `F1.lenRightCocycleCfgStmt_of_refl` and of `ae_b5PlusArc`). The
  reflection is applied to the off-tip local limits (`isVagueLimitOnR_neg`) at the times `t` and
  `u + s`, and the field of the configuration unzipped by `u` at time `s` is identified with the
  field at time `u + s` in regular coordinates (`RegUnif.capCocycleRegStmt_holds`, D33, proved).
  The side limits of the shifted driver exist since no real point is swallowed
  (`F1.ae_shift_alive_all`). No global limit (`CfgFlowRegStmt`) and no tip input is used.

The identifications are own elementary arguments (the paper only says "by symmetry").
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace LocLen

open B2 B5 RegUnif

/-- **Reflection of a side arc** (deterministic, own elementary): if the regularized averages of
`y'` at `t` are those of `y` at `−t` and `y` has a local limit off `0`, then the left open arc of
`y'` for the driver `−D` has the length of the right open arc of `y` for `D`. -/
theorem arcLen_reflect_side {γ : ℝ} {y y' : FieldSample}
    (havg : ∀ (k : ℕ) (t : ℝ), avgReg y' k (t : ℂ) = avgReg y k ((-t : ℝ) : ℂ))
    {ν : Measure ℝ} (hν : IsVagueLimitOnR ({0}ᶜ) (bdryApprox γ y) ν) {D : ℝ → ℝ} {s a b : ℝ}
    (hs : 0 ≤ s) (hl : Tendsto (fun x : ℝ => (fwdMap D s x).re) (𝓝[<] (0 : ℝ)) (𝓝 a))
    (hm : Tendsto (fun x : ℝ => (fwdMap D s x).re) (𝓝[>] (0 : ℝ)) (𝓝 b)) :
    arcLen γ y' (sideImages (-D) s).1 0 = arcLen γ y 0 (sideImages D s).2 := by
  have hν' := isVagueLimitOnR_neg havg isOpen_compl_singleton hν
  rw [F1.sideImages_reflect_swap hs hl hm]
  dsimp only
  rw [arcLen_eq_of_isVagueLimitOnR hν' (fun z hz hz0 => by
      simp only [mem_singleton_iff, neg_eq_zero] at hz0
      linarith [hz.2]),
    arcLen_eq_of_isVagueLimitOnR hν (fun z hz hz0 => by
      rw [mem_singleton_iff] at hz0; linarith [hz.1]),
    Measure.map_apply measurable_neg measurableSet_Ioo]
  congr 1
  ext t; simp only [mem_preimage, mem_Ioo]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ}
  {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

/-- **Additivity of the open-arc right length along the capacity flow, all times** (no tip
input), by reflection of `ae_leftCocycleArc`. -/
theorem ae_rightCocycleArc (hκ : 0 < κ) (hκ4 : κ < 4)
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) :
    ∀ᵐ ω ∂P, ∀ u s : ℝ, 0 ≤ u → 0 ≤ s →
      (unzipLengthsArc (Real.sqrt κ) (cfg κ B X ω) (u + s)).2 =
        (unzipLengthsArc (Real.sqrt κ) (cfg κ B X ω) u).2 +
          (unzipLengthsArc (Real.sqrt κ) (zipCapDown (Real.sqrt κ) u (cfg κ B X ω)) s).2 := by
  have hB' : IsBrownianReal (negB B) P := hB.neg
  have hX' : IsFreeGFFModConstH (reflX X) P := isFreeGFFModConstH_reflRaw hX
  have hind' := indepFun_neg_reflRaw hind
  filter_upwards [ae_leftCocycleArc hκ hκ4 hB' hX' hind',
    ae_all_iff.2 fun n : ℕ => unifLocalStmt_holds (T := (n : ℝ) + 1) hκ hκ4 (by positivity)
      hB hX hind,
    ae_all_iff.2 fun n : ℕ => capCocycleRegStmt_holds (κ := κ) (T := (n : ℝ) + 1) hB hX hind
      (by positivity),
    ae_all_iff.2 fun n : ℕ => capCocycleRegStmt_holds (κ := κ) (T := (n : ℝ) + 1) hB' hX' hind'
      (by positivity),
    ae_forall_isRegularSample (γ := Real.sqrt κ) hB hX hind,
    ae_isRegularSample_ofFun_h0rev hX κ, ae_drive_good hB κ,
    RS.ae_real_alive hB hκ hκ4.le, F1.ae_shift_alive_all κ hκ hκ4.le P B hB] with
    ω hLc hloc hC hC' hreg hx hdr halive hsh u s hu hs
  obtain ⟨hWc, hW0⟩ := hdr
  obtain ⟨Fx, hFx⟩ := hx
  obtain ⟨n, hn⟩ := exists_nat_ge (u + s)
  have hus : u + s ≤ (n : ℝ) + 1 := by linarith
  have hcfg : cfg κ (negB B) (reflX X) ω =
      (reflRaw (ofFun (h0rev κ) + X ω), -drive κ B ω) :=
    Prod.ext (reflRaw_add_ofFun_h0rev κ (X ω)).symm (drive_negB κ B ω)
  -- the local limit of the field at time `t ≤ n + 1`, and its reflection
  have hloc' : ∀ t : ℝ, 0 ≤ t → t ≤ (n : ℝ) + 1 → ∃ ν : Measure ℝ,
      IsVagueLimitOnR ({0}ᶜ) (bdryApprox (Real.sqrt κ) (unzippedField (Real.sqrt κ)
        (ofFun (h0rev κ) + X ω, drive κ B ω) t)) ν := by
    intro t ht htn
    obtain ⟨ν, hν, -⟩ := hloc n t ⟨ht, htn⟩
    rw [h0f_eq_unzippedField] at hν
    exact ⟨ν, hν⟩
  have havg : ∀ t : ℝ, 0 ≤ t → ∀ (k : ℕ) (v : ℝ),
      avgReg (unzippedField (Real.sqrt κ) (reflRaw (ofFun (h0rev κ) + X ω), -drive κ B ω) t)
          k (v : ℂ) =
        avgReg (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + X ω, drive κ B ω) t) k
          ((-v : ℝ) : ℂ) := by
    intro t ht k v
    obtain ⟨Ft, hFt⟩ := (hreg t ht).1
    exact avgReg_unzippedField_reflRaw_neg_real (x := ofFun (h0rev κ) + X ω)
      (W := drive κ B ω) hWc hW0 ht hFx hFt k v
  -- the lengths of `cfg` at times `t ≤ n + 1`
  have E : ∀ t : ℝ, 0 ≤ t → t ≤ (n : ℝ) + 1 →
      (unzipLengthsArc (Real.sqrt κ) (cfg κ (negB B) (reflX X) ω) t).1 =
        (unzipLengthsArc (Real.sqrt κ) (cfg κ B X ω) t).2 := by
    intro t ht htn
    obtain ⟨l, m, hl, hm⟩ := F1.exists_tendsto_sideImages_of_alive (W := drive κ B ω) ht
      fun x hx => halive x hx t ht
    obtain ⟨ν, hν⟩ := hloc' t ht htn
    rw [hcfg]
    exact arcLen_reflect_side (havg t ht) hν ht hl hm
  -- the newly unzipped piece
  have Epiece : (unzipLengthsArc (Real.sqrt κ)
        (zipCapDown (Real.sqrt κ) u (cfg κ (negB B) (reflX X) ω)) s).1 =
      (unzipLengthsArc (Real.sqrt κ) (zipCapDown (Real.sqrt κ) u (cfg κ B X ω)) s).2 := by
    obtain ⟨hrg, -, -⟩ := hC n u s hu hs hus
    obtain ⟨hrg', -, -⟩ := hC' n u s hu hs hus
    have hdrv : (zipCapDown (Real.sqrt κ) u (cfg κ (negB B) (reflX X) ω)).2 =
        -(zipCapDown (Real.sqrt κ) u (cfg κ B X ω)).2 := by
      rw [hcfg]
      funext r
      simp only [zipCapDown, Pi.neg_apply]
      show -drive κ B ω (u + max r 0) - -drive κ B ω u = -(drive κ B ω (u + max r 0) - drive κ B ω u)
      ring
    have e1 : (unzipLengthsArc (Real.sqrt κ)
          (zipCapDown (Real.sqrt κ) u (cfg κ (negB B) (reflX X) ω)) s).1 =
        arcLen (Real.sqrt κ)
          (unzippedField (Real.sqrt κ) (cfg κ (negB B) (reflX X) ω) (u + s))
          (sideImages (-(zipCapDown (Real.sqrt κ) u (cfg κ B X ω)).2) s).1 0 := by
      rw [← hdrv]
      exact arcLen_congr (B3d.avgReg_eq_of_regEq hrg') _ _
    have e2 : (unzipLengthsArc (Real.sqrt κ) (zipCapDown (Real.sqrt κ) u (cfg κ B X ω)) s).2 =
        arcLen (Real.sqrt κ) (unzippedField (Real.sqrt κ) (cfg κ B X ω) (u + s))
          0 (sideImages (zipCapDown (Real.sqrt κ) u (cfg κ B X ω)).2 s).2 :=
      arcLen_congr (B3d.avgReg_eq_of_regEq hrg) _ _
    rw [e1, e2]
    obtain ⟨l, m, hl, hm⟩ := F1.exists_tendsto_sideImages_of_alive
      (W := (zipCapDown (Real.sqrt κ) u (cfg κ B X ω)).2) hs
      fun x hx => hsh u hu x hx s hs
    obtain ⟨ν, hν⟩ := hloc' (u + s) (add_nonneg hu hs) hus
    rw [hcfg]
    exact arcLen_reflect_side (havg (u + s) (add_nonneg hu hs)) hν hs hl hm
  have h := hLc u s hu hs
  rw [E (u + s) (add_nonneg hu hs) hus, E u hu (by linarith), Epiece] at h
  exact h

/-- **The open-arc capacity cocycle in the `Γ⁰` picture holds** (both sides; no tip input). -/
theorem lenPairCocycleCfgArc_holds : LenPairCocycleCfgArcStmt := by
  intro κ Ω _ P _ B X hκ hκ4 hB hX hind
  filter_upwards [ae_leftCocycleArc hκ hκ4 hB hX hind, ae_rightCocycleArc hκ hκ4 hB hX hind] with
    ω h1 h2 u s hu hs
  exact ⟨h1 u s hu hs, h2 u s hu hs⟩

end LocLen
end QuantumZipper

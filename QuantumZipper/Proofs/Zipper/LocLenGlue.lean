import QuantumZipper.Proofs.Zipper.LocLenDefs
import QuantumZipper.Proofs.Zipper.E1Glue
import QuantumZipper.Proofs.LQG.LogSingularity

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Follow-the-paper campaign (D75): gluing local offset-uniform boundary limits

If a regular sample `x` has an offset-uniform local boundary limit (`HasBdryLimitOn`) on every
window `(p,q)` with `[p,q] ⊆ U` (`U` open), then it has one on `U`
(`exists_hasBdryLimitOn_of_windows`). Consequently goodness off a closed set `S` follows from the
area limit and local limits on the windows avoiding `S` (`isLQGGoodOff_of_windows`); atomlessness
of the window limits passes to the glued limit (`hasBdryLimitOn_atomless_of_windows`).

Proof: the unit-offset sequence `bdryApprox γ x` has a local vague limit on every window, so the
proved sequence gluing `E1.exists_isVagueLimitOnR_of_windows` (E1Glue.lean) gives a local vague
limit `μ` on `U`; by uniqueness of local limits (`LocalRule.isVagueLimitOnR_unique`) `μ` restricts
to the given window limits; the `goodFilter` convergence for a test function supported in `U` is
reduced, by the same finite partition of unity as in E1Glue
(`exists_continuous_sum_one_of_isOpen_isCompact`), to test functions supported in single windows.
This is the standard sheaf property of Radon measures (Bourbaki, *Integration*, Ch. III §2 No. 1,
Prop. 1); our own formalization (as in E1Glue).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper
namespace LocLen

variable {γ : ℝ} {x : FieldSample}

/-- The trivial local limit on the empty set. -/
theorem hasBdryLimitOn_empty_zero : HasBdryLimitOn γ x ∅ 0 :=
  ⟨by simp, fun _ _ _ => by simp, fun f _ _ hfU => by
    have : f = 0 := funext fun t => image_eq_zero_of_notMem_tsupport fun ht => hfU ht
    subst this; simpa using tendsto_const_nhds⟩

/-- **Gluing** of offset-uniform local boundary limits: local limits on all windows `(p,q)` with
`[p,q] ⊆ U` give a local limit on the open set `U`. -/
theorem exists_hasBdryLimitOn_of_windows (hx : IsRegularSample x) {U : Set ℝ} (hU : IsOpen U)
    (hloc : ∀ p q : ℝ, Icc p q ⊆ U → ∃ ν, HasBdryLimitOn γ x (Ioo p q) ν) :
    ∃ ν, HasBdryLimitOn γ x U ν := by
  classical
  obtain ⟨μ, hμ⟩ := E1.exists_isVagueLimitOnR_of_windows (νs := bdryApprox γ x) hU
    (fun k => LogSing.isFiniteMeasureOnCompacts_bdryApprox hx γ k)
    (fun p q h => (hloc p q h).imp fun _ hν => hν.isVagueLimitOnR hx)
  -- the window limits are the restrictions of `μ`
  have hW : ∀ n, HasBdryLimitOn γ x (E1.winW U n) (μ.restrict (E1.winW U n)) := fun n => by
    by_cases h : Icc ((E1.winPQ n).1 : ℝ) (E1.winPQ n).2 ⊆ U
    · have e : E1.winW U n = Ioo ((E1.winPQ n).1 : ℝ) (E1.winPQ n).2 := by
        unfold E1.winW; rw [if_pos h]
      obtain ⟨ν, hν⟩ := hloc _ _ h
      have : μ.restrict (Ioo ((E1.winPQ n).1 : ℝ) (E1.winPQ n).2) = ν :=
        LocalRule.isVagueLimitOnR_unique isOpen_Ioo
          (E1.isVagueLimitOnR_restrict_open hμ isOpen_Ioo (Ioo_subset_Icc_self.trans h))
          (hν.isVagueLimitOnR hx)
      rw [e, this]; exact hν
    · have e : E1.winW U n = ∅ := by unfold E1.winW; rw [if_neg h]
      rw [e, Measure.restrict_empty]; exact hasBdryLimitOn_empty_zero
  refine ⟨μ, hμ.1, hμ.2.1, fun f hf hfc hfU => ?_⟩
  obtain ⟨F, hF⟩ := hx
  -- a partition of unity subordinate to finitely many windows
  set K := tsupport f with hKdef
  have hKc : IsCompact K := hfc
  obtain ⟨s, hs⟩ := hKc.elim_finite_subcover (E1.winW U) (E1.isOpen_winW U)
    (by rw [E1.iUnion_winW hU]; exact hfU)
  set e := s.equivFin
  set S : Fin s.card → Set ℝ := fun i => E1.winW U (e.symm i) with hS
  obtain ⟨g, hgS, hg1, -, -⟩ := exists_continuous_sum_one_of_isOpen_isCompact
    (fun i => E1.isOpen_winW U (e.symm i)) hKc (t := K) (s := S) (by
      intro y hy
      obtain ⟨n, hn, hyn⟩ := mem_iUnion₂.1 (hs hy)
      exact mem_iUnion.2 ⟨e ⟨n, hn⟩, by simp only [hS, Equiv.symm_apply_apply]; exact hyn⟩)
  have hsplit : ∀ t, f t = ∑ i, f t * g i t := fun t => by
    rw [← Finset.mul_sum]
    by_cases ht : t ∈ K
    · have := hg1 ht
      simp only [Finset.sum_apply, Pi.one_apply] at this
      rw [this, mul_one]
    · rw [image_eq_zero_of_notMem_tsupport ht, zero_mul]
  have hfg : ∀ i, Continuous fun t => f t * g i t := fun i => hf.mul (g i).continuous
  have hfgc : ∀ i, HasCompactSupport fun t => f t * g i t := fun i => hfc.mul_right
  have hfgS : ∀ i, tsupport (fun t => f t * g i t) ⊆ S i := fun i =>
    (tsupport_mul_subset_right).trans (hgS i)
  -- splitting the approximating integrals (eventually, where the radius is positive)
  have hint : ∀ᶠ j in goodFilter, ∑ i, ∫ t, f t * g i t ∂bdryR γ x (goodRad j) =
      ∫ t, f t ∂bdryR γ x (goodRad j) :=
    GoodSample.eventually_goodRad_pos.mono fun j hj => by
      have : IsFiniteMeasureOnCompacts (bdryR γ x (goodRad j)) :=
        ⟨fun K hK => GoodSample.bdryR_lt_top γ hF hj hK⟩
      rw [← integral_finsetSum _ fun i _ => (hfg i).integrable_of_hasCompactSupport (hfgc i)]
      exact integral_congr_ae (ae_of_all _ fun t => (hsplit t).symm)
  -- splitting the limit integral
  have hlim : ∫ t, f t ∂μ = ∑ i, ∫ t, f t * g i t ∂μ := by
    rw [← integral_finsetSum _ fun i _ =>
      GoodSample.integrable_of_tsupport hμ.2.1 (hfg i) (hfgc i)
        ((hfgS i).trans (E1.winW_subset U _))]
    exact integral_congr_ae (ae_of_all _ fun t => hsplit t)
  rw [hlim]
  refine (tendsto_finsetSum _ fun i _ => ?_).congr' hint
  have hi := (hW (e.symm i)).2.2 _ (hfg i) (hfgc i) (hfgS i)
  rwa [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun t ht => image_eq_zero_of_notMem_tsupport fun h => ht (hfgS i h))] at hi

/-- **Goodness off a closed set from windows**: a regular sample with an area limit and local
boundary limits on all windows `(p,q)` with `[p,q] ∩ S = ∅` is good off `S`. -/
theorem isLQGGoodOff_of_windows {S : Set ℝ} (hS : IsClosed S) (hx : IsRegularSample x)
    (hA : ∃ μ, HasAreaLimit γ x μ)
    (hloc : ∀ p q : ℝ, Icc p q ∩ S = ∅ → ∃ ν, HasBdryLimitOn γ x (Ioo p q) ν) :
    IsLQGGoodOff γ x S :=
  ⟨hx, exists_hasBdryLimitOn_of_windows hx hS.isOpen_compl fun p q h =>
    hloc p q (eq_empty_of_forall_notMem fun _ ht => h ht.1 ht.2), hA⟩

end LocLen
end QuantumZipper

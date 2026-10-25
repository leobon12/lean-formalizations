import SupercriticalLQGUniqueness.B2.DG20Lim.CoordSpace

 

set_option autoImplicit false
noncomputable section

open Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

private abbrev PositiveRational := Set.Ioi (0 : ℚ)

private instance : SecondCountableTopology (PositiveRational → ℝ≥0∞) := inferInstance
private instance : CompactSpace (PositiveRational → ℝ≥0∞) := inferInstance

 



theorem exists_positive_ratio_subseq
    (a : ℕ → PositiveRational → ℝ)
    (ha : ∀ n r, 0 < a n r)
    (hb : ∀ r, ∃ lo hi : ℝ, 0 < lo ∧ lo ≤ hi ∧
      ∀ᶠ n in atTop, lo ≤ a n r ∧ a n r ≤ hi) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∃ c : PositiveRational → Set.Ioi (0 : ℝ),
        ∀ r, Tendsto (fun n => a (ψ n) r) atTop (nhds (c r : ℝ)) := by
  let A : ℕ → PositiveRational → ℝ≥0∞ := fun n r => ENNReal.ofReal (a n r)
  obtain ⟨u, -, ψ, hψ, hconv⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set (PositiveRational → ℝ≥0∞))).tendsto_subseq (x := A)
      (fun _ => Set.mem_univ _)
  have hcoord (r : PositiveRational) :
      Tendsto (fun n => A (ψ n) r) atTop (nhds (u r)) :=
    by simpa [Function.comp_def] using ((continuous_apply r).tendsto u).comp hconv
  have hfin (r : PositiveRational) : u r ≠ ∞ := by
    obtain ⟨lo, hi, hlo, hlohi, hbound⟩ := hb r
    have he : ∀ᶠ n in atTop, A (ψ n) r ≤ ENNReal.ofReal hi := by
      filter_upwards [hψ.tendsto_atTop.eventually hbound] with n hn
      exact ENNReal.ofReal_le_ofReal hn.2
    have hlim : u r ≤ ENNReal.ofReal hi :=
      le_of_tendsto_of_tendsto (hcoord r) tendsto_const_nhds he
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hlim
  have hpositive (r : PositiveRational) : 0 < (u r).toReal := by
    obtain ⟨lo, hi, hlo, hlohi, hbound⟩ := hb r
    have he : ∀ᶠ n in atTop, ENNReal.ofReal lo ≤ A (ψ n) r := by
      filter_upwards [hψ.tendsto_atTop.eventually hbound] with n hn
      exact ENNReal.ofReal_le_ofReal hn.1
    have hlim : ENNReal.ofReal lo ≤ u r :=
      le_of_tendsto_of_tendsto tendsto_const_nhds (hcoord r) he
    have hu : 0 < u r := lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hlo) hlim
    exact ENNReal.toReal_pos hu.ne' (hfin r)
  refine ⟨ψ, hψ, fun r => ⟨(u r).toReal, hpositive r⟩, ?_⟩
  intro r
  have ht := (ENNReal.tendsto_toReal (hfin r)).comp (hcoord r)
  convert ht using 1
  funext n
  exact (ENNReal.toReal_ofReal (le_of_lt (ha (ψ n) r))).symm

end SupercriticalLQGUniqueness.B2.DG20Lim

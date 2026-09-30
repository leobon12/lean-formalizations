import QuantumZipper.Proofs.Zipper.F2Weld
import QuantumZipper.Proofs.Loewner.WeldingConsistency
import QuantumZipper.Proofs.Thm14.WeldingData
import QuantumZipper.Proofs.Thm14.FromThm13
import QuantumZipper.Proofs.RS.RohdeSchrammSimple

/-!
# F2 (Theorem 1.3): welding times of the reverse `SLE_κ` hull (`WeldTimesStmt`)

Node **F2**, deterministic welding input. We prove `F2.WeldTimesStmt` (`F2Weld.lean`)
unconditionally: for the Theorem 1.3 driver `W = drive κ B ω` (`= √κ · B`, `0 < κ < 4`) and
`T > 0`, almost surely every pair `xm < 0 < xp` identified by the boundary extension of
`revMap W T`, with common image on the hull `η_T ∪ {0}`, is the pair
`(0₋(u), 0₊(u)) = (zeroMinus W u, zeroPlus W u)` of the two points swallowed at a common
reverse time `u ∈ [0,T]`, and it lies in `[0₋(T), 0₊(T)]`.

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, §1.3–§1.4 (the welding
homeomorphism of the reverse SLE hull; the two sides of the tip) and §5.1 (the preimage of the
hull is the interval of swallowed points, sliced by the times at which the flow reaches the real
axis). The statement of `WeldTimesStmt` itself does *not* constrain `u` beyond existence: the
time is recovered as the common hitting time of `xm` (which is what the flow structure forces).

## Route

For a fixed path with `IsSimpleCurveHull (revHull W T)` (a.s. by Rohde–Schramm,
`Thm14FromThm13.ae_isSimpleCurveHull_revHull` + the proved `RS.rohdeSchrammSimple`), let `F` be
the Carathéodory extension of `revMap W T` (`CaraR.revMapCaratheodory`) and `a = 0₋(T)`,
`b = 0₊(T)`, `φ = weldingHom W T`. Then:

1. if the common image is `0`, the fibre structure of `F` (clause 7 of
   `Blueprint.IsCaratheodoryRevExt`) and the boundary structure force `xm = a` and `xp = b`, so
   `u = T` works;
2. if the image is non-real (`∈ ℍ`, which is what `hmem` gives for the non-zero case), the real
   image criterion (clause 6) gives `a < xm < b`, `a < xp < b`;
3. `u := (realHitTime W xm).toReal ∈ [0,T]` satisfies `0₋(u) = xm` (`B5.hitTime_spec`, the
   deterministic B5 node); `u > 0` because `xm < 0`;
4. the welding homeomorphism is consistent across times (`WeldingConsistency.weldingHom_eq_of_le`),
   so `φ_T(xm) = φ_u(0₋(u)) = 0₊(u)` (the last by clause 5 of the extension at time `u`);
5. `F xp = F xm` and `xm = 0₋(u) ∈ [a,0]` force `xp = φ_T(xm) = 0₊(u)`
   (`Thm14WeldingData.eq_weldingHom_of_car`).

Own assembly of proved inputs (the analytic content is CaraR / Rohde–Schramm / the Carathéodory
boundary correspondence, as cited); no new hypothesis is used. The plus-side mirror of the
`B5.zeroMinus` facts is *not* needed: the plus side is read off the Carathéodory extension
(clauses 5 and 6 and `weldingHom_le_zeroPlus_of_car`).
-/

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal ComplexConjugate

namespace QuantumZipper
namespace F2

/-! ## The deterministic welding-time structure -/

/-- **Deterministic welding times.** Let `W` be continuous with `W 0 = 0` and `T > 0`, and
suppose the reverse hull `revHull W T` is a simple curve hull. Then any pair `xm < 0 < xp`
identified by the boundary extension of `revMap W T`, whose common image lies in
`revHull W T ∪ {0}`, is the pair of points `(0₋(u), 0₊(u))` swallowed at a common time
`u ∈ [0,T]`, and lies in `[0₋(T), 0₊(T)]`. -/
theorem weldTimes_of_simpleCurveHull {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {T : ℝ} (hT : 0 < T) (hK : IsSimpleCurveHull (revHull W T)) {xm xp : ℝ} (hxm : xm < 0)
    (hxp : 0 < xp) (heq : revMapBdry W T xm = revMapBdry W T xp)
    (hmem : revMapBdry W T xm ∈ insert 0 (revHull W T)) :
    ∃ u ∈ Icc (0 : ℝ) T, xm = zeroMinus W u ∧ xp = zeroPlus W u ∧
      zeroMinus W T ≤ xm ∧ xp ≤ zeroPlus W T := by
  obtain ⟨FT, hFT⟩ := CaraR.revMapCaratheodory W hW hW0 T hT hK
  have hne := WeldingConsistency.simpleCurveHull_nonempty hK
  obtain ⟨ha, hb, -⟩ := WeldingConsistency.car_basic hW hT hFT hne
  have hbdry : ∀ x : ℝ, revMapBdry W T x = FT x := fun x =>
    Thm14WeldingData.revMapBdry_eq_of_car hFT x
  have hreal : ∀ x : ℝ, (revMapBdry W T x).im = 0 ↔
      x ≤ zeroMinus W T ∨ zeroPlus W T ≤ x := by
    intro x
    rw [hbdry x]
    exact hFT.2.2.2.2.2.1 x
  rcases eq_or_ne (revMapBdry W T xm) 0 with hw0 | hw0
  · -- the common image is `0`: the fibre over `0` is `{0₋(T), 0₊(T)}`
    have hxm_a : xm = zeroMinus W T :=
      WeldingConsistency.car_eq_zeroMinus hFT ha hb hxm.le (by rw [← hbdry xm]; exact hw0)
    have hxp_b : xp = zeroPlus W T := by
      have h1 : FT ((zeroMinus W T : ℝ) : ℂ) = FT ((xp : ℝ) : ℂ) := by
        rw [hFT.2.2.2.1, ← hbdry xp, ← heq, hw0]
      rcases (hFT.2.2.2.2.2.2 _ (Thm14WeldingData.hbar_ofReal _) _
        (Thm14WeldingData.hbar_ofReal _)).1 h1 with h | ⟨s, hs, h' | h'⟩
      · exact absurd (Complex.ofReal_injective h) (by linarith)
      · rw [Complex.ofReal_injective h'.2, ← Complex.ofReal_injective h'.1, hFT.2.2.2.2.1]
      · exact absurd (Complex.ofReal_injective h'.1) fun hc => by
          have hφ := (Thm14WeldingData.weldingHom_mem_of_car hFT hs).1
          linarith
    exact ⟨T, ⟨hT.le, le_rfl⟩, hxm_a, hxp_b, hxm_a.symm.le, hxp_b.le⟩
  · -- the common image is in the hull, hence non-real
    have hwH : 0 < (revMapBdry W T xm).im := by
      rcases hmem with h | h
      · exact absurd h hw0
      · exact h.1
    have hwH' : 0 < (revMapBdry W T xp).im := by rw [← heq]; exact hwH
    have hlt_a : zeroMinus W T < xm := by
      by_contra hc
      exact absurd ((hreal xm).2 (Or.inl (not_lt.1 hc))) (ne_of_gt hwH)
    have hxm_b : xm < zeroPlus W T := by
      by_contra hc
      exact absurd ((hreal xm).2 (Or.inr (not_lt.1 hc))) (ne_of_gt hwH)
    have hxp_a : zeroMinus W T < xp := by
      by_contra hc
      exact absurd ((hreal xp).2 (Or.inl (not_lt.1 hc))) (ne_of_gt hwH')
    have hxp_b : xp < zeroPlus W T := by
      by_contra hc
      exact absurd ((hreal xp).2 (Or.inr (not_lt.1 hc))) (ne_of_gt hwH')
    -- the time at which `xm` is swallowed
    obtain ⟨-, hu, hzu⟩ := B5.hitTime_spec hW hW0 hT hK (x := xm) ⟨hlt_a, hxm.le⟩
    set u : ℝ := (realHitTime W xm).toReal with hu_def
    have huI : u ∈ Icc (0 : ℝ) T := by rw [hu_def]; exact hu
    have hzu' : zeroMinus W u = xm := by rw [hu_def]; exact hzu
    have hu0 : 0 < u := by
      rcases eq_or_lt_of_le huI.1 with h | h
      · rw [← h, B5.zeroMinus_zero_time hW hW0] at hzu'
        linarith
      · exact h
    have hKu := B5.isSimpleCurveHull_of_le hW hW0 hT hK hu0 huI.2
    obtain ⟨Fu, hFu⟩ := CaraR.revMapCaratheodory W hW hW0 u hu0 hKu
    -- the welded partner of `0₋(u)` at time `T` is `0₊(u)`
    have hweld_u : weldingHom W T (zeroMinus W u) = zeroPlus W u := by
      rw [WeldingConsistency.weldingHom_eq_of_le CaraR.revMapCaratheodory
        CoreArc.loewnerSubhullsOfArc hW hW0 hT hK hu0 huI.2 (x := zeroMinus W u)
        ⟨le_rfl, WeldingUniqueness.zeroMinus_nonpos W u⟩]
      exact hFu.2.2.2.2.1
    have hweld_xm : weldingHom W T xm = zeroPlus W u := by rw [← hzu', hweld_u]
    have hs_xm : xm ∈ Icc (zeroMinus W T) 0 := ⟨hlt_a.le, hxm.le⟩
    have hxy : FT xp = FT xm := by rw [← hbdry xp, ← hbdry xm, heq]
    have hxp_eq : xp = zeroPlus W u := by
      rw [Thm14WeldingData.eq_weldingHom_of_car hFT hs_xm hxp.le hxy, hweld_xm]
    exact ⟨u, huI, hzu'.symm, hxp_eq, hlt_a.le, hxp_b.le⟩

/-! ## The a.s. statement for the Theorem 1.3 driver -/

/-- **`WeldTimesStmt` from Rohde–Schramm simplicity.** -/
theorem weldTimesStmt_of_RS (hRSS : Blueprint.RohdeSchrammSimple) : WeldTimesStmt := by
  intro κ hκ hκ4 T hT Ω _ P _ B hB
  filter_upwards [Thm14FromThm13.ae_isSimpleCurveHull_revHull hRSS hκ hκ4 hT P B hB,
    hB.cont, hB.eval_zero_ae_eq_zero] with ω hK hc h0
  have hWc : Continuous (drive κ B ω) := Thm14FromThm13.continuous_drive hc
  have hW0 : drive κ B ω 0 = 0 := by simp [drive, h0]
  exact fun xm xp => weldTimes_of_simpleCurveHull hWc hW0 hT hK

/-- **`WeldTimesStmt` (unconditional).** Rohde–Schramm simplicity of the reverse hull is
proved (`RS.rohdeSchrammSimple`). -/
theorem weldTimesStmt : WeldTimesStmt := weldTimesStmt_of_RS RS.rohdeSchrammSimple

end F2
end QuantumZipper

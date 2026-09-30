import QuantumZipper.Proofs.Section5.Prop16D4WInNice
import QuantumZipper.Proofs.Section5.Prop16MarkovMaskSetup
import QuantumZipper.Proofs.Section5.Prop16ShiftGoodPalm

/-!
# Proposition 1.6, node C′ (masked): the Markov-coupling node, pieces (a)–(d)

Task P16-MARKOVMASK2. The M7 assembly (`Prop16MarkovMaskSetup.lean`,
`prop16_markovSetup_at`) already produces, at the boundary point `x`, a mixed GFF `Y`, a D3⁺
`Setup γ γ r' ρ₀ P₀ (palmCField X x) Ξ g` with `g` harmonic on the half-disc, and the per-measure
identity `Y ω (μ(·−x)) = X'(μ) − μ(ℂ)X'(ρ₀') + ∫ g(·+x) dμ` for admissible `μ` carried by
`closedBall 0 r'`. This file supplies the remaining pieces of `Prop16NodeCMarkovMaskStmt`:

* **(a)** `prop16LocNice_of_mixedGFF`: *any* mixed GFF on `D`, free on `[c,d]`, is a.s. locally
  nice on `D ∪ (a,b)` — local niceness is determined by the countably many values at the
  admissible folded circles (`locCircSet`), an event whose probability is fixed by the law of
  those values, and all mixed GFFs have the same such law (`locGood_map_eq_of_isMixedGFF`). So
  the statement proved for one witness field by the domain Markov coupling
  (`prop16LocNiceStmt_of_coupling`) transfers to the `Y` of M7. This is the masked node C′'s
  `IsLocNiceOn` clause, which the M7 coupling alone does not provide.
* **(c)** `exists_vagueLimit_zoomFree_palmMixedField` (**proved unconditionally**): the zoomed
  Palm-shifted field of a locally nice sample has a local area measure on `D − x`. This is
  `Prop16PalmShiftGood.lean`'s deterministic core fed with the now-proved representative
  `palmCircRepStmt_proved` (the Palm shift is `−2 log|·−x|` plus a continuous function on `D`).
* **(b)+(d)** `Prop16PalmMarkovCouplingStmt`: the remaining node, exactly
  `Prop16NodeCMarkovMaskStmt` with the `IsLocNiceOn` clause removed, i.e. the D3⁺ data together
  with the a.s. `AgreeNear` between the zoomed Palm-shifted mixed field and the model field, the
  local area limit, and the a.e.-measurability of the model's local scale.
  `Prop16PalmShiftHarmStmt` isolates the missing *mathematical* input: on measures carried by a
  small ball about `x`, the Palm shift `G_D(x, x+·)` is `−2 log‖·‖` plus a function
  `ψ` with `ψ ∘ foldH` harmonic near `0`, which is then absorbed into the `g` of M7 (keeping the
  `Setup`'s `harm` clause, the constant `𝔥₀(x)` also being absorbed). Together with the M7
  identity this gives the `AgreeNear`; the remaining work is the `translate`/`evalReg`
  bookkeeping (`fcAgree_translate`, `CircAgree`) and the countable-family assembly of the M7
  a.s. identities over the dyadic circles.

Assembly: `prop16NodeCMarkovMaskStmt_of_palmMarkov` (node C′ input from (a) + (b)+(c)+(d)) and
`theorem1_6_of_palmMarkov` (Proposition 1.6 from the coupling, the Palm mask identity, D3⁺(i) in
N2 form and the Palm-Markov node).

Sources: Sheffield, arXiv:1012.4797, proof of Prop. 1.6 (p. 25) ("the conditional law of `h` given
`x` is the GFF plus `(γ/2)G_D(x,·)`; zooming in at `x` …"); Sheffield, *Gaussian free fields for
mathematicians*, PTRF 139 (2007), Thm 2.17 (domain Markov property). The law transfer (a), the
bookkeeping and the isolation of (b) are own arguments (the project's `Prop16LocGood` route; the
paper works with the continuum field directly).

Status (task P16-MARKOVMASK2): (a) and (c) are proved here; the `evalReg` bridge, the countable
assembly and (d) are proved in `Prop16MarkovMask2Agree.lean` (`prop16PalmMarkovCoupling_of_harm`);
the only open input is `Prop16PalmShiftHarmStmt` (assembly: `Prop16MarkovMask2Final.lean`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper

namespace Prop16Asm

open Prop16Area Prop16Area.G Prop16Area.Meas TV Factorization

/-! ## (a) Local niceness of an arbitrary mixed GFF -/

/-- **Node LOCNICE for an arbitrary mixed GFF** (piece (a) of node C′): locally niceness on
`D ∪ (a,b)` does not depend on the mixed GFF, only on the (common) law of its values at the
admissible folded circles. This is `prop16LocNiceStmt_of_coupling` with the hypothesis
`Prop16Data` weakened to `IsMixedGFF D (realSet (Icc c d)) X P` together with a probability
measure: only those fields are used by the transfer. -/
theorem prop16LocNice_of_mixedGFF (hA : Prop16MixedFreeLocCouplingStmt) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {D : Set ℂ} {c d a b : ℝ} (hgeo : K3.Prop16Geometry D c d) (hab : a < b)
    (hca : c ≤ a) (hbd : b ≤ d) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → FieldSample) (hP : IsProbabilityMeasure P)
    (hX : IsMixedGFF D (realSet (Icc c d)) X P) :
    ∀ᵐ ω ∂P, IsLocNiceOn γ (D ∪ realSet (Ioo a b)) (X ω) := by
  haveI := hP
  obtain ⟨W, hWo, hWV⟩ := locGood_exists_open hgeo hca hbd
  obtain ⟨Ω₀, _, _, P₀, Y, Xf, hP₀, hY, hXf, hag⟩ := hA D c d a b hgeo hab hca hbd
  haveI := hP₀
  set V := D ∪ realSet (Ioo a b) with hVdef
  have hVW : ∀ {s : Set ℂ}, s ⊆ Hbar → (s ⊆ V ↔ s ⊆ W) := fun {s} hs =>
    ⟨fun h u hu => by rw [← hWV] at h; exact (h hu).1,
      fun h u hu => by rw [← hWV]; exact ⟨h hu, hs hu⟩⟩
  have hsubH : ∀ (n k : ℕ) (z : ℂ), closedBall (dyadicRoundC n z) (radius k) ∩ Hbar ⊆ Hbar :=
    fun _ _ _ => inter_subset_right
  let I := {m : Measure ℂ // m ∈ locCircSet V}
  have : Countable I := (locCircSet_countable V).to_subtype
  have hadm : ∀ i : I, IsAdmissibleDual D (mixedSpace D (realSet (Icc c d))) i.1 := by
    rintro ⟨_, n, k, z, hz, hsub, rfl⟩
    exact locGood_isAdmissible_circle hgeo hca hbd hWo hWV
      (CircleCont.dyadicRoundC_mem_Hbar hz n) (radius_pos k) ((hVW (hsubH n k z)).1 hsub)
  have hlaw := locGood_map_eq_of_isMixedGFF hX hY (fun i : I => i.1) hadm
  have hS : ∀ᵐ ω₀ ∂P₀, ω₀ ∈ {ω₀ | IsLQGGood γ (Xf ω₀) ∧
      (∀ a : ℝ, qAreaMeasure γ (Xf ω₀) (Metric.ball 0 a ∩ H) < ⊤) ∧
      (∀ U : Set ℂ, IsOpen U → U ⊆ H → U.Nonempty → 0 < qAreaMeasure γ (Xf ω₀) U) ∧
      ∃ ψ : ℂ → ℝ, ContinuousOn ψ V ∧
      Prop16Area.G.CircAgree V (Y ω₀) (Xf ω₀ + ofFun ψ)} := by
    filter_upwards [AreaOffsets.ae_isLQGGood hXf hγ hγ2,
      FinArea.ae_qAreaMeasure_ball_lt_top hXf (P := P₀) hγ hγ2,
      PositivityArea.ae_forall_pos_qAreaMeasure hXf (P := P₀) hγ hγ2, hag]
      with ω₀ h1 h2 h3 h4 using ⟨h1, h2, h3, h4⟩
  have hmF : Measurable fun ω (i : I) => X ω i.1 :=
    measurable_pi_iff.2 fun i => hX.measurable_coord _
  have hmG : Measurable fun ω (i : I) => Y ω i.1 :=
    measurable_pi_iff.2 fun i => hY.measurable_coord _
  filter_upwards [locGood_ae_exists_of_map_eq hmF.aemeasurable hmG hlaw hS] with ω hω
  obtain ⟨ω₀, ⟨hgood, hfin, hpos, ψ, hψ, hag'⟩, hFG⟩ := hω
  refine ⟨W, hWo, hWV, Xf ω₀, ψ, hgood, hfin, hpos, hψ, fun n k z hz hsub => ?_⟩
  have hsubV := (hVW (hsubH n k z)).2 hsub
  have h1 := congrFun hFG ⟨_, n, k, z, hz, hsubV, rfl⟩
  exact h1.trans (hag' n k z hz hsubV)

/-! ## (c) The local area limit (unconditional) -/

/-- **Piece (c): the zoomed Palm-shifted field has a local area measure.** Deterministic core of
`Prop16PalmShiftGood.lean` fed with the proved Palm representative (`palmCircRepStmt_proved`):
for a sample locally nice on `D ∪ (a,b)` and `x ∈ (c,d)`, the zoomed Palm-shifted field
`(X + (γ/2)G_D(x,·))(· + x) + C/γ + 𝔥₀(x)` has a local area measure on `D − x`. -/
theorem exists_vagueLimit_zoomFree_palmMixedField {γ : ℝ} {D : Set ℂ} {c d a b x : ℝ}
    {h0 : ℂ → ℝ} (hgeo : K3.Prop16Geometry D c d) (hx : x ∈ Ioo c d) {Ω : Type}
    (X : Ω → FieldSample) (ω : Ω) (hloc : IsLocNiceOn γ (D ∪ realSet (Ioo a b)) (X ω)) (C : ℝ) :
    ∃ μ, IsVagueLimitOn (zoomDomain D x)
      (areaApprox γ (zoomFree γ C h0 (palmMixedField γ D (realSet (Icc c d)) X x) (ω, x))) μ := by
  obtain ⟨hDo, -, -, hDH, -⟩ := id hgeo
  obtain ⟨ψ, hψ, hagP⟩ := palmCircRepStmt_proved D c d x hgeo hx
  exact exists_limit_zoomFree_palmMixedField X ω hDo hDH hψ hagP hloc C

/-! ## Bookkeeping for (b): the radius and the harmonic correction of `g` -/

/-- **Shrinking the D3⁺ radius and absorbing a Neumann-harmonic function (and a constant) into
`g`.** This is the step that lets the harmonic representative `ψ` of the Palm shift and the
constant `𝔥₀(x)` of `zoomFree` be carried by the `g` of the D3⁺ setup: harmonicity is preserved,
`gmeas` survives because the conditioning σ-algebra grows as the radius shrinks
(`outsideSigma_anti_radius`), and no other field of the structure mentions the radius. -/
theorem D3Plus.Setup.mono_absorb {γ α r : ℝ} {ρ₀ : Measure ℂ} {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → FieldSample} {E' : Type} [MeasurableSpace E'] {Ξ : Ω → E'}
    {g : Ω → ℂ → ℝ} (h : D3Plus.Setup γ α r ρ₀ P X Ξ g) {r' : ℝ} (hr' : 0 < r') (hr'r : r' ≤ r)
    {ψ : ℂ → ℝ} (hψ : InnerProductSpace.HarmonicOnNhd (fun z => ψ (foldH z))
      (Metric.ball 0 r')) (c : ℝ) :
    D3Plus.Setup γ α r' ρ₀ P X Ξ (fun ω z => g ω z + ψ z + c) where
  hγ := h.hγ
  hγ2 := h.hγ2
  hα := h.hα
  hr := hr'
  hX := h.hX
  hΞ := h.hΞ
  hind := h.hind
  hρ := h.hρ
  hρ1 := h.hρ1
  hρB := measure_mono_null (Metric.ball_subset_ball hr'r) h.hρB
  harm := fun ω z hz => by
    have h1 : InnerProductSpace.HarmonicAt (fun w => g ω (foldH w)) z :=
      h.harm ω z (Metric.ball_subset_ball hr'r hz)
    have h2 : InnerProductSpace.HarmonicAt (fun w => ψ (foldH w)) z := hψ z hz
    have h3 := (h1.add h2).add (InnerProductSpace.harmonicAt_const c)
    convert h3 using 1
    funext w
    simp only [Pi.add_apply]
  gmeas := fun z => by
    have hc : Measurable[D3Plus.condSigma Ξ X r] fun _ : Ω => (ψ z + c) := measurable_const
    have h2 := ((h.gmeas z).add hc).mono
      (sup_le_sup_left (K3.outsideSigma_anti_radius X 0 hr'r) _) le_rfl
    convert h2 using 1
    funext ω
    simp only [Pi.add_apply]
    ring

/-! ## Bookkeeping for (b): the countable assembly of the per-measure M7 identity -/

/-! ## (b) The missing input, isolated -/

/-- **(b) The Palm shift near `x` is `−2 log‖· − x‖` plus a Neumann-harmonic function.** On the
admissible measures carried by a small ball about `x`, the Palm shift (the mixed Green function
`G_D(x, ·)`, read through `mixedGreenSample`) splits as `γ(−log‖·−x‖)` plus the pairing with a
single function `ψ` whose `foldH`-composition is harmonic on the ball. This is the local
statement `G_D(x,·) = −2 log|· − x| + harmonic` of Sheffield, arXiv:1012.4797, proof of Prop. 1.6
(p. 25) (there `x` is a free-arc point, so `G_D(x,·) + 2 log|· − x|` is harmonic across the arc).

Not yet formalized. Route: `palmPsi_eq_kernel` (`Prop16ShiftGoodPalm.lean`) gives
`palmPsi D S x (x+w) = mixedGreenK K k x (x+w) = neumannH x (x+w) + k x (x+w)` with
`neumannH x (x+w) = neumannH 0 w = −2 log‖w‖` (`neumannH_add_real`), so it remains to show that
`w ↦ k x (x + w)` is harmonic; for the M6 kernel `k = mixedK D S s`,
`mixedK x (x+w) = 2 log max (s,‖w‖) + mixedG D S s (x, x+w)`, a circle average of the truncated
log kernel plus an inner product of Riesz vectors, whose mean-value property is the analogue of
`K3.harmonicOnNhd_inner_mixCurve` for the curve `z ↦ rieszVec (foldedCircle z s)` (Weyl's lemma,
`K3.harmonicOnNhd_of_meanValue`). -/
def Prop16PalmShiftHarmStmt : Prop :=
  ∀ (γ : ℝ) (D : Set ℂ) (c d x : ℝ), 0 < γ → γ < 2 → K3.Prop16Geometry D c d →
    x ∈ Ioo c d → ∃ r > 0, (Metric.ball (x : ℂ) r ∩ H) ⊆ D ∧ ∃ ψ : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd (fun z => ψ (foldH z)) (Metric.ball 0 r) ∧
      ∀ μ : Measure ℂ, IsAdmissibleH μ → μ (Metric.closedBall 0 r)ᶜ = 0 →
        (γ / 2) * mixedGreenSample D (realSet (Icc c d)) x (μ.map (· + (x : ℂ))) =
          ∫ w, (γ * -Real.log ‖w‖ + ψ w) ∂μ

/-- **The Palm-Markov coupling node** (pieces (b), (c) and (d) of node C′):
`Prop16NodeCMarkovMaskStmt` without the `IsLocNiceOn` clause, which (a) then attaches.

Two further obstacles beyond `Prop16PalmShiftHarmStmt` when assembling this from M7
(`prop16_markovSetup_at`), both about comparing a raw value with a *regularized* one:

* `zoomFree` is built from `translate`, i.e. it evaluates its field through `evalReg`, while
  `zoomModel` is evaluated raw at the folded circle. The bridge is
  `evalReg_eq_of_circAgree` (`Prop16LocalAgree.lean`): it suffices that the Palm-shifted field
  `Z = Y + (γ/2) G_D(x,·)` and the untranslated model field `X + ofFun (γ(−log‖·−x‖) + g(·) + …)`
  satisfy `CircAgree W` on the circles near `x`, which is the M7 identity plus
  `Prop16PalmShiftHarmStmt`. The tools for the remaining part are in place:
  `RegSample.ae_isRegularSample` makes the free field of the coupling a.s. regular,
  `IsRegularWith.evalReg_fc_of_mem` identifies `evalReg` with the raw value at folded circles, and
  `GoodSample.evalReg_add_ofFun_fc` gives
  `evalReg (X + ofFun φ) (fc w r) = X (fc w r) + smoothFun φ w r` for `φ` continuous on `Hbar`.
  The remaining technicality is that the log term `−log‖·−x‖` of the Palm shift is *not*
  continuous on `Hbar` at `x` (it is only integrable against the circles), so
  `evalReg_add_ofFun_fc` needs a variant for an integrable log singularity.
* the M7 identity is a.s. per measure (`∀ μ … → ∀ᵐ ω`); over the countably many dyadic folded
  circles inside `closedBall 0 r` (parametrized by `(n, k, a, b) ∈ ℕ × ℕ × ℤ × ℤ`) the a.s.
  sets must be intersected, and the result transported to `Hbar`-centred circles
  (`agreeNear_of_hbarCenters`) to build the `AgreeNear`.

Piece (d) additionally uses the joint measurability of `(ω, z) ↦ g ω z` (the `Setup` only
records `∀ z, Measurable[condSigma Ξ X r] fun ω => g ω z`) to get
`Measurable fun ω => zoomModel γ γ C ρ₀ (X' ω) (g ω)`, which
`Prop16Area.Meas.aemeasurable_scaleParamOn` needs. -/
def Prop16PalmMarkovCouplingStmt : Prop :=
  ∀ (γ : ℝ) (D : Set ℂ) (c d a b : ℝ) (h0 : ℂ → ℝ), 0 < γ → γ < 2 → K3.Prop16Geometry D c d →
    a < b → c ≤ a → b ≤ d →
    ∀ x ∈ Ioo a b, ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (P₀ : Measure Ω₀)
      (Y : Ω₀ → FieldSample) (r : ℝ) (ρ₀ : Measure ℂ) (X' : Ω₀ → FieldSample) (E' : Type)
      (_ : MeasurableSpace E') (Ξ : Ω₀ → E') (g : Ω₀ → ℂ → ℝ),
      IsProbabilityMeasure P₀ ∧ IsMixedGFF D (realSet (Icc c d)) Y P₀ ∧
      D3Plus.Setup γ γ r ρ₀ P₀ X' Ξ g ∧ D3Plus.halfDisc r ⊆ zoomDomain D x ∧
      (∀ᵐ ω ∂P₀, ∀ C : ℝ,
        D3Plus.AgreeNear (zoomFree γ C h0 (palmMixedField γ D (realSet (Icc c d)) Y x) (ω, x))
          (D3Plus.zoomModel γ γ C ρ₀ (X' ω) (g ω)) r ∧
        ∃ μ, IsVagueLimitOn (zoomDomain D x)
          (areaApprox γ (zoomFree γ C h0 (palmMixedField γ D (realSet (Icc c d)) Y x) (ω, x))) μ) ∧
      ∀ C : ℝ, AEMeasurable (fun ω => scaleParamOn γ
        (D3Plus.zoomModel γ γ C ρ₀ (X' ω) (g ω)) (D3Plus.halfDisc r)) P₀

/-! ## Assembly -/

/-- **Node C′ input from (a) and the Palm-Markov node** (own bookkeeping): the local niceness of
the mixed GFF produced by the coupling is transferred by `prop16LocNice_of_mixedGFF`. -/
theorem prop16NodeCMarkovMaskStmt_of_palmMarkov (hA : Prop16MixedFreeLocCouplingStmt)
    (h : Prop16PalmMarkovCouplingStmt) : Prop16NodeCMarkovMaskStmt := by
  intro γ D c d a b h0 hγ hγ2 hgeo hab hca hbd x hx
  obtain ⟨Ω₀, _, P₀, Y, r, ρ₀, X', E', _, Ξ, g, hP₀, hY, hS, hsub, hag, hsc⟩ :=
    h γ D c d a b h0 hγ hγ2 hgeo hab hca hbd x hx
  exact ⟨Ω₀, _, P₀, Y, r, ρ₀, X', E', _, Ξ, g, hP₀, hY,
    prop16LocNice_of_mixedGFF hA hγ hγ2 hgeo hab hca hbd P₀ Y hP₀ hY, hS, hsub, hag, hsc⟩

end Prop16Asm

end QuantumZipper

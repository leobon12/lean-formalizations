import InteractingSLE.GFF.LocalSets.BoundaryVanishing
import InteractingSLE.GFF.LocalSets.AbsContBoundary


/-!
# Absolute continuity at a common boundary on two domains (specification Proposition 3.4 (ii))

Source: `source/ig1-specification.pdf`, §3.1, Proposition 3.4 (ii) and its proof (pp. 46–47;
transcription `source/spec/p001-048.md#prop-3.4`, `#prop-3.4-proof`, L1159–L1167): for simply
connected `D₁, D₂`, `U ⊆ D₁ ∩ D₂` bounded, a neighbourhood `U'` of `cl U` with
`D₁ ∩ U' = D₂ ∩ U'` and `F₁ − F₂ → 0` at `∂Dᵢ ∩ U'`, the laws of `(hᵢ + Fᵢ)|_U` are mutually
absolutely continuous.

Route (PROVE-LS-A handoff §3 (C)): with `V = D₁ ∩ int U' = D₂ ∩ int U'`, the Markov decomposition
of `hᵢ` on `V` writes `(hᵢ + Fᵢ)|_U = Zᵢ|_U + Yᵢ`, `Zᵢ` a zero-boundary GFF on `V` independent of
`Yᵢ = uᵢ|_U`, `uᵢ` harmonic on `V`; by Proposition 3.3 (`ae_tendsto_markov_sub_frontier`, with
`K = Dᵢ ∖ V` at positive distance from `∂V ∩ int U'`) `uᵢ − Fᵢ → 0` at `∂V ∩ int U'`. The
translates of the law of `Z|_U` by such shifts are mutually absolutely continuous
(`map_restrictAdd_absolutelyContinuous_of_tendsto_frontier`, PROVE-LS-A: Caccioppoli truncation and
Cameron–Martin for `L²` limits), and the mixture lemma `map_add_absolutelyContinuous_of_indepFun`
concludes.

## Main results

* `exists_restrictAdd_decomposition_tendsto`: the local Markov decomposition with boundary
  vanishing of the harmonic part;
* `map_restrictAdd_absolutelyContinuous_of_common`: one direction, for a common open piece `V`;
* `map_restrictAdd_mutuallyAbsCont_boundary`: **Proposition 3.4 (ii)** (source form).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set TopologicalSpace
open LQGMetric
open SupercriticalConformalCovariance.GM24 (smoothDist smoothDist_apply integrable_test_mul)

namespace InteractingSLE
namespace GFF

/-- A frontier point of `W ⊆ D` outside `cl(D ∖ W)` is a frontier point of `D`. -/
lemma mem_frontier_diff_of_mem_frontier {D W : Set ℂ} (hD : IsOpen D) (hW : IsOpen W)
    (hWD : W ⊆ D) {z : ℂ} (hz : z ∈ frontier W) (hzK : z ∉ closure (D \ W)) :
    z ∈ frontier D \ closure (D \ W) := by
  refine ⟨⟨closure_mono hWD hz.1, fun hzD => ?_⟩, hzK⟩
  rw [hD.interior_eq] at hzD
  have hzW : z ∉ W := fun h => hz.2 (by rwa [hW.interior_eq])
  exact hzK (subset_closure ⟨hzD, hzW⟩)

/-- **Local Markov decomposition with boundary vanishing.** For a zero-boundary GFF `h` on a simply
connected domain `D ≠ ℂ`, `F` harmonic on `D` and open `U ≤ W ≤ D`:
`(h + F)|_U = Z|_U + Y` with `Z` a zero-boundary GFF on `W`, `Y ⫫ Z|_U`, and almost surely
`Y = u|_U` with `u` harmonic on `W` and `u − F → 0` at every point of `∂W ∩ U''` outside
`cl(D ∖ W)` (Proposition 3.3 for the harmonic part). -/
theorem exists_restrictAdd_decomposition_tendsto {D W U : Opens ℂ} (hWD : W ≤ D) (hUW : U ≤ W)
    (hDc : IsConnected (D : Set ℂ)) (hDs : IsSimplyConnected (D : Set ℂ))
    (hDne : (D : Set ℂ) ≠ univ) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistOn D} (hh : IsZeroBoundaryGFF D h P) {F : ℂ → ℝ}
    (hF : InnerProductSpace.HarmonicOnNhd F D) {U'' : Set ℂ}
    (hfr : ∀ z ∈ frontier (W : Set ℂ) ∩ U'', z ∉ closure ((D : Set ℂ) \ W)) :
    ∃ (Z' : Ω → DistOn W) (Y : Ω → DistOn U), IsZeroBoundaryGFF W Z' P ∧ Measurable Y ∧
      IndepFun (fun ω => restrictDist U (Z' ω)) Y P ∧
      (∀ᵐ ω ∂P, ∃ u : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd u W ∧ Y ω = smoothDist U u ∧
        ∀ z ∈ frontier (W : Set ℂ) ∩ U'',
          Tendsto (fun x => u x - F x) (𝓝[(W : Set ℂ)] z) (𝓝 0)) ∧
      ∀ ω, restrictAdd U (h ω) F = restrictDist U (Z' ω) + Y ω := by
  have hD : ZBAdmissible D := zbAdmissible_of_isSimplyConnected hDc hDs hDne
  obtain ⟨G, hGm, hG⟩ := exists_markovMap hWD hD
  have hd := hG hh
  have hFW : InnerProductSpace.HarmonicOnNhd F W := hF.mono hWD
  have hcF : ContinuousOn F U :=
    ((contDiffOn_of_harmonicOnNhd (n := 0) hFW).continuousOn).mono hUW
  let Y : Ω → DistOn U := fun ω => restrictDist U (h ω - G (h ω)) + smoothDist U F
  have hsub : Measurable fun T : DistOn D => T - G T :=
    measurable_distOn_iff.2 fun φ =>
      (measurable_distOn_apply φ).sub ((measurable_distOn_apply φ).comp hGm)
  have hΦ : Measurable fun T : DistOn D => restrictDist U T + smoothDist U F :=
    measurable_distOn_iff.2 fun φ =>
      ((measurable_distOn_apply φ).comp (measurable_restrictDist U)).add_const _
  have hYm : Measurable Y := hΦ.comp (hsub.comp hh.measurable)
  refine ⟨fun ω => restrictDist W (G (h ω)), Y, hd.isZeroBoundaryGFF, hYm, ?_, ?_, ?_⟩
  · have hi := hd.indepFun.comp (measurable_restrictDist U) hΦ
    refine hi.congr (Filter.Eventually.of_forall fun ω => ?_) Filter.EventuallyEq.rfl
    exact (restrictDist_restrictDist hUW hWD _).symm
  · filter_upwards [hd.ae_harmonic, ae_tendsto_markov_sub_frontier hWD hDc hDs hDne hh hd] with
      ω ⟨g, hg, hgrep⟩ hlim
    refine ⟨fun x => g x + F x, hg.add hFW, ?_, fun z hz => ?_⟩
    · have hcg : ContinuousOn g U :=
        ((contDiffOn_of_harmonicOnNhd (n := 0) hg).continuousOn).mono hUW
      ext φ
      have e1 : restrictDist U (h ω - G (h ω)) φ = ∫ x, φ x * g x := by
        rw [← restrictDist_restrictDist hUW hWD, restrictDist_apply, hgrep, coe_testIncl hUW]
        simp only [mul_comm]
      simp only [Y, add_apply]
      rw [e1, smoothDist_apply hcF, smoothDist_apply (Y := fun x => g x + F x) (hcg.add hcF),
        ← integral_add (integrable_test_mul hcg φ) (integrable_test_mul hcF φ)]
      simp only [mul_add]
    · have hz' := mem_frontier_diff_of_mem_frontier D.isOpen W.isOpen hWD hz.1 (hfr z hz)
      refine (hlim g hg hgrep z hz').congr fun x => ?_
      ring
  · intro ω
    simp only [restrictAdd, Y, restrictDist_restrictDist hUW hWD, restrictDist_sub]
    abel

/-- **Absolute continuity across two domains with a common piece** (one direction). Let `V` be
open, `V ⊆ D₁ ∩ D₂` (simply connected domains `≠ ℂ`), `U ⊆ V` bounded open, `U''` open with
`cl U ⊆ U''`, such that the frontier points of `V` in `U''` are away from `cl(Dᵢ ∖ V)`, and
`F₁ − F₂ → 0` at `∂V ∩ U''` (within `V`). Then `law((h₁ + F₁)|_U) ≪ law((h₂ + F₂)|_U)`. -/
theorem map_restrictAdd_absolutelyContinuous_of_common {D₁ D₂ U V : Opens ℂ} (hV₁ : V ≤ D₁)
    (hV₂ : V ≤ D₂) (hD₁c : IsConnected (D₁ : Set ℂ)) (hD₁s : IsSimplyConnected (D₁ : Set ℂ))
    (hD₁ne : (D₁ : Set ℂ) ≠ univ) (hD₂c : IsConnected (D₂ : Set ℂ))
    (hD₂s : IsSimplyConnected (D₂ : Set ℂ)) (hD₂ne : (D₂ : Set ℂ) ≠ univ)
    (hUb : Bornology.IsBounded (U : Set ℂ)) (hUV : U ≤ V) {U'' : Set ℂ} (hU''o : IsOpen U'')
    (hUU'' : closure (U : Set ℂ) ⊆ U'')
    (hfr₁ : ∀ z ∈ frontier (V : Set ℂ) ∩ U'', z ∉ closure ((D₁ : Set ℂ) \ V))
    (hfr₂ : ∀ z ∈ frontier (V : Set ℂ) ∩ U'', z ∉ closure ((D₂ : Set ℂ) \ V))
    {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] {P₁ : Measure Ω₁}
    {P₂ : Measure Ω₂} [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    {h₁ : Ω₁ → DistOn D₁} {h₂ : Ω₂ → DistOn D₂} (hh₁ : IsZeroBoundaryGFF D₁ h₁ P₁)
    (hh₂ : IsZeroBoundaryGFF D₂ h₂ P₂) {F₁ F₂ : ℂ → ℝ}
    (hF₁ : InnerProductSpace.HarmonicOnNhd F₁ D₁) (hF₂ : InnerProductSpace.HarmonicOnNhd F₂ D₂)
    (hbd : ∀ z ∈ frontier (V : Set ℂ) ∩ U'',
      Tendsto (fun x => F₁ x - F₂ x) (𝓝[(V : Set ℂ)] z) (𝓝 0)) :
    P₁.map (fun ω => restrictAdd U (h₁ ω) F₁) ≪ P₂.map (fun ω => restrictAdd U (h₂ ω) F₂) := by
  obtain ⟨Z₁', Y₁, hZ₁, hY₁m, hi₁, hY₁ae, he₁⟩ :=
    exists_restrictAdd_decomposition_tendsto hV₁ hUV hD₁c hD₁s hD₁ne hh₁ hF₁ hfr₁
  obtain ⟨Z₂', Y₂, hZ₂, hY₂m, hi₂, hY₂ae, he₂⟩ :=
    exists_restrictAdd_decomposition_tendsto hV₂ hUV hD₂c hD₂s hD₂ne hh₂ hF₂ hfr₂
  have hadm : ZBAdmissible V :=
    zbAdmissible_mono hV₁ (zbAdmissible_of_isSimplyConnected hD₁c hD₁s hD₁ne)
  have hZ₁m : Measurable fun ω => restrictDist U (Z₁' ω) :=
    (measurable_restrictDist U).comp hZ₁.measurable
  have hZ₂m : Measurable fun ω => restrictDist U (Z₂' ω) :=
    (measurable_restrictDist U).comp hZ₂.measurable
  have hlaw : P₁.map (fun ω => restrictDist U (Z₁' ω)) =
      P₂.map (fun ω => restrictDist U (Z₂' ω)) := by
    have e1 := Measure.map_map (μ := P₁) (measurable_restrictDist U (D := V)) hZ₁.measurable
    have e2 := Measure.map_map (μ := P₂) (measurable_restrictDist U (D := V)) hZ₂.measurable
    change P₁.map (restrictDist U ∘ Z₁') = P₂.map (restrictDist U ∘ Z₂')
    rw [← e1, ← e2, hZ₁.map_eq hZ₂]
  have hshift : ∀ y : DistOn U, Measurable fun T : DistOn U => T + y := fun y =>
    (measurable_add_distOn U).comp (measurable_id.prodMk measurable_const)
  set S : Set (DistOn U) := {y | ∃ w : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w V ∧
      y = smoothDist U w ∧ ∀ z ∈ frontier (V : Set ℂ) ∩ U'',
        Tendsto (fun x => w x - F₁ x) (𝓝[(V : Set ℂ)] z) (𝓝 0)} with hS
  have hSac : ∀ y ∈ S, ∀ y' ∈ S,
      (P₁.map fun ω => restrictDist U (Z₁' ω)).map (· + y) ≪
        (P₁.map fun ω => restrictDist U (Z₁' ω)).map (· + y') := by
    rintro _ ⟨w, hw, rfl, hwlim⟩ _ ⟨w', hw', rfl, hw'lim⟩
    rw [Measure.map_map (hshift _) hZ₁m, Measure.map_map (hshift _) hZ₁m]
    exact map_restrictAdd_absolutelyContinuous_of_tendsto_frontier hadm hUb hUV hU''o hUU'' hZ₁
      hw hw' fun z hz => by
        have := (hwlim z hz).sub (hw'lim z hz)
        rw [sub_zero] at this
        exact this.congr fun x => by ring
  have hY₁S : ∀ᵐ ω ∂P₁, Y₁ ω ∈ S := hY₁ae.mono fun ω ⟨u, hu, hYu, hlim⟩ => ⟨u, hu, hYu, hlim⟩
  have hY₂S : ∀ᵐ ω ∂P₂, Y₂ ω ∈ S := hY₂ae.mono fun ω ⟨u, hu, hYu, hlim⟩ =>
    ⟨u, hu, hYu, fun z hz => by
      have := (hlim z hz).sub (hbd z hz)
      rw [sub_zero] at this
      exact this.congr fun x => by ring⟩
  have key := map_add_absolutelyContinuous_of_indepFun (measurable_add_distOn U) hZ₁m hY₁m hZ₂m
    hY₂m hi₁ hi₂ hlaw S hSac hY₁S hY₂S
  have e₁ : (fun ω => restrictAdd U (h₁ ω) F₁) = fun ω => restrictDist U (Z₁' ω) + Y₁ ω :=
    funext he₁
  have e₂ : (fun ω => restrictAdd U (h₂ ω) F₂) = fun ω => restrictDist U (Z₂' ω) + Y₂ ω :=
    funext he₂
  rw [e₁, e₂]
  exact key


/-- **Proposition 3.4 (ii) (Absolute continuity, boundary).** Let `D₁, D₂ ≠ ℂ` be simply connected
domains with `D₁ ∩ D₂ ≠ ∅`, `hᵢ` a zero-boundary GFF on `Dᵢ`, `Fᵢ` harmonic on `Dᵢ`, and
`U ⊆ D₁ ∩ D₂` a bounded simply connected domain. If some neighbourhood `U'` of `cl U` satisfies
`D₁ ∩ U' = D₂ ∩ U'` and `F₁ − F₂` tends to zero as one approaches the points of `∂D₁ ∩ U'`
(`= ∂D₂ ∩ U'`), then the laws of `(h₁ + F₁)|_U` and `(h₂ + F₂)|_U` are mutually absolutely
continuous. (`D₁ ∩ D₂ ≠ ∅` and the connectivity of `U` are not used.) -/
theorem map_restrictAdd_mutuallyAbsCont_boundary {D₁ D₂ U : Opens ℂ} {U' : Set ℂ}
    (hD₁c : IsConnected (D₁ : Set ℂ)) (hD₁s : IsSimplyConnected (D₁ : Set ℂ))
    (hD₁ne : (D₁ : Set ℂ) ≠ univ) (hD₂c : IsConnected (D₂ : Set ℂ))
    (hD₂s : IsSimplyConnected (D₂ : Set ℂ)) (hD₂ne : (D₂ : Set ℂ) ≠ univ)
    (_h12 : ((D₁ : Set ℂ) ∩ D₂).Nonempty) (hUb : Bornology.IsBounded (U : Set ℂ))
    (_hUc : IsConnected (U : Set ℂ)) (_hUs : IsSimplyConnected (U : Set ℂ))
    (hUD : (U : Set ℂ) ⊆ (D₁ : Set ℂ) ∩ D₂) (hU' : U' ∈ 𝓝ˢ (closure (U : Set ℂ)))
    (hD12 : (D₁ : Set ℂ) ∩ U' = (D₂ : Set ℂ) ∩ U')
    {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] {P₁ : Measure Ω₁}
    {P₂ : Measure Ω₂} [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    {h₁ : Ω₁ → DistOn D₁} {h₂ : Ω₂ → DistOn D₂} (hh₁ : IsZeroBoundaryGFF D₁ h₁ P₁)
    (hh₂ : IsZeroBoundaryGFF D₂ h₂ P₂) {F₁ F₂ : ℂ → ℝ}
    (hF₁ : InnerProductSpace.HarmonicOnNhd F₁ D₁) (hF₂ : InnerProductSpace.HarmonicOnNhd F₂ D₂)
    (hbd : ∀ z ∈ frontier (D₁ : Set ℂ) ∩ U',
      Tendsto (fun x => F₁ x - F₂ x) (𝓝[(D₁ : Set ℂ)] z) (𝓝 0)) :
    P₁.map (fun ω => restrictAdd U (h₁ ω) F₁) ≪ P₂.map (fun ω => restrictAdd U (h₂ ω) F₂) ∧
      P₂.map (fun ω => restrictAdd U (h₂ ω) F₂) ≪ P₁.map (fun ω => restrictAdd U (h₁ ω) F₁) := by
  have hint : closure (U : Set ℂ) ⊆ interior U' := subset_interior_iff_mem_nhdsSet.2 hU'
  let V : Opens ℂ := ⟨(D₁ : Set ℂ) ∩ interior U', D₁.isOpen.inter isOpen_interior⟩
  have h21 : ∀ y ∈ (D₂ : Set ℂ), y ∈ U' → y ∈ (D₁ : Set ℂ) := fun y hy hyU' => by
    have : y ∈ (D₁ : Set ℂ) ∩ U' := hD12 ▸ ⟨hy, hyU'⟩
    exact this.1
  have hV₁ : V ≤ D₁ := fun y hy => hy.1
  have hV₂ : V ≤ D₂ := fun y hy => by
    have : y ∈ (D₂ : Set ℂ) ∩ U' := hD12 ▸ ⟨hy.1, interior_subset hy.2⟩
    exact this.1
  have hUV : U ≤ V := fun y hy => ⟨(hUD hy).1, hint (subset_closure hy)⟩
  have hcl₁ : closure ((D₁ : Set ℂ) \ V) ⊆ (interior U')ᶜ :=
    closure_minimal (fun y hy hyU' => hy.2 ⟨hy.1, hyU'⟩) isOpen_interior.isClosed_compl
  have hcl₂ : closure ((D₂ : Set ℂ) \ V) ⊆ (interior U')ᶜ :=
    closure_minimal (fun y hy hyU' => hy.2 ⟨h21 y hy.1 (interior_subset hyU'), hyU'⟩)
      isOpen_interior.isClosed_compl
  have hfr₁ : ∀ z ∈ frontier (V : Set ℂ) ∩ interior U', z ∉ closure ((D₁ : Set ℂ) \ V) :=
    fun z hz hc => hcl₁ hc hz.2
  have hfr₂ : ∀ z ∈ frontier (V : Set ℂ) ∩ interior U', z ∉ closure ((D₂ : Set ℂ) \ V) :=
    fun z hz hc => hcl₂ hc hz.2
  have hbdV : ∀ z ∈ frontier (V : Set ℂ) ∩ interior U',
      Tendsto (fun x => F₁ x - F₂ x) (𝓝[(V : Set ℂ)] z) (𝓝 0) := by
    intro z hz
    have hzD := (mem_frontier_diff_of_mem_frontier D₁.isOpen V.isOpen hV₁ hz.1 (hfr₁ z hz)).1
    exact (hbd z ⟨hzD, interior_subset hz.2⟩).mono_left (nhdsWithin_mono z hV₁)
  refine ⟨map_restrictAdd_absolutelyContinuous_of_common hV₁ hV₂ hD₁c hD₁s hD₁ne hD₂c hD₂s
    hD₂ne hUb hUV isOpen_interior hint hfr₁ hfr₂ hh₁ hh₂ hF₁ hF₂ hbdV,
    map_restrictAdd_absolutelyContinuous_of_common hV₂ hV₁ hD₂c hD₂s hD₂ne hD₁c hD₁s
    hD₁ne hUb hUV isOpen_interior hint hfr₂ hfr₁ hh₂ hh₁ hF₂ hF₁ fun z hz => ?_⟩
  have := (hbdV z hz).neg
  rw [neg_zero] at this
  exact this.congr fun x => by ring


end GFF
end InteractingSLE

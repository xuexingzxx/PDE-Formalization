import MyProject.LpJensen
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Towards Fréchet–Kolmogorov / Rellich (Evans §5.7), foundations

This file builds the measure-theoretic groundwork for the Fréchet–Kolmogorov compactness criterion.
The first need is **reflection invariance** of the Lebesgue volume on `ℝⁿ`: the map `y ↦ x − y` is
measure-preserving (negation has `|det| = 1`).  Mathlib provides no `IsNegInvariant` instance, so we
derive negation-invariance from `map_addHaar_smul` (`-y = (-1)·y`, and `|(-1)ⁿ|⁻¹ = 1`).
-/

open MeasureTheory Module
open scoped ENNReal

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

namespace Sobolev

/-- **Negation preserves Lebesgue volume on `ℝⁿ`.**  Since `-y = (-1) • y` and the Haar measure
rescales by `|(-1)ⁿ|⁻¹ = 1` under scalar multiplication, negation is measure-preserving. -/
lemma measurePreserving_neg_euclidean :
    MeasurePreserving (fun y : ℝⁿ => -y) (volume : Measure ℝⁿ) volume := by
  refine ⟨measurable_neg, ?_⟩
  have h1 : (fun y : ℝⁿ => -y) = fun y => (-1 : ℝ) • y := by funext y; rw [neg_one_smul]
  rw [h1, Measure.map_addHaar_smul volume (show (-1 : ℝ) ≠ 0 by norm_num)]
  simp

/-- **Reflection invariance of the volume integral**: `∫ F(x − y) dy = ∫ F(y) dy`.  The map
`y ↦ x − y` is the composite of the (measure-preserving) translation `y ↦ y − x` and negation. -/
lemma lintegral_comp_sub_left {F : ℝⁿ → ℝ≥0∞} (hF : Measurable F) (x : ℝⁿ) :
    ∫⁻ y, F (x - y) ∂volume = ∫⁻ y, F y ∂volume := by
  have hcomp := measurePreserving_neg_euclidean.comp (measurePreserving_sub_right volume x)
  have hfun : (fun y : ℝⁿ => -y) ∘ (fun y => y - x) = fun y => x - y := by
    funext y; simp [neg_sub]
  rw [hfun] at hcomp
  exact hcomp.lintegral_comp hF

/-- **Reflection invariance of the `Lᵖ` seminorm**: `‖η(x − ·)‖_p = ‖η‖_p`. -/
lemma eLpNorm_comp_sub_left {η : ℝⁿ → ℝ} (hη : AEStronglyMeasurable η volume) (p : ℝ≥0∞)
    (x : ℝⁿ) : eLpNorm (fun y => η (x - y)) p volume = eLpNorm η p volume := by
  have hmp : MeasurePreserving (fun y : ℝⁿ => x - y) volume volume := by
    have hcomp := measurePreserving_neg_euclidean.comp (measurePreserving_sub_right volume x)
    have hfun : (fun y : ℝⁿ => -y) ∘ (fun y => y - x) = fun y => x - y := by
      funext y; simp [neg_sub]
    rwa [hfun] at hcomp
  exact eLpNorm_comp_measurePreserving hη hmp

/-- **Hölder bound for the convolution integrand** — the analytic core of Young's `L∞` estimate.
For conjugate real exponents `P, Q`, the `L¹` mass of `y ↦ η(x−y)·u(y)` is bounded by the
(`x`-independent, by reflection invariance) `L^Q`-content of `η` times the `L^P`-content of `u`. -/
lemma lintegral_enorm_mul_reflect_le {η u : ℝⁿ → ℝ} (hη : Continuous η)
    (hu : AEStronglyMeasurable u volume) {P Q : ℝ} (hPQ : P.HolderConjugate Q) (x : ℝⁿ) :
    ∫⁻ y, ‖η (x - y)‖ₑ * ‖u y‖ₑ ∂volume
      ≤ (∫⁻ y, ‖η y‖ₑ ^ Q ∂volume) ^ (1 / Q) * (∫⁻ y, ‖u y‖ₑ ^ P ∂volume) ^ (1 / P) := by
  have hηr : Continuous fun y : ℝⁿ => η (x - y) := hη.comp (continuous_const.sub continuous_id)
  have hf : AEMeasurable (fun y : ℝⁿ => ‖η (x - y)‖ₑ) volume := hηr.enorm.aemeasurable
  have hg : AEMeasurable (fun y : ℝⁿ => ‖u y‖ₑ) volume := hu.enorm
  have hol := ENNReal.lintegral_mul_le_Lp_mul_Lq volume hPQ.symm hf hg
  have href : ∫⁻ y, ‖η (x - y)‖ₑ ^ Q ∂volume = ∫⁻ y, ‖η y‖ₑ ^ Q ∂volume :=
    lintegral_comp_sub_left (F := fun z => ‖η z‖ₑ ^ Q)
      ((ENNReal.continuous_rpow_const.comp hη.enorm).measurable) x
  rw [href] at hol
  exact hol

/-- **Hölder bound for an integral product** (general form): `‖∫ g·u‖ ≤ ‖g‖_Q · ‖u‖_P` for
conjugate exponents `P, Q`.  The reusable tool behind both Young's inequality and the
equicontinuity modulus of mollification. -/
lemma enorm_integral_mul_le {g u : ℝⁿ → ℝ} (hg : AEStronglyMeasurable g volume)
    (hu : AEStronglyMeasurable u volume) {P Q : ℝ} (hPQ : P.HolderConjugate Q) :
    ‖(∫ y, g y * u y ∂volume)‖ₑ
      ≤ eLpNorm g (ENNReal.ofReal Q) volume * eLpNorm u (ENNReal.ofReal P) volume := by
  have hQ0 : 0 < Q := hPQ.symm.pos
  have hP0 : 0 < P := hPQ.pos
  have heQ : eLpNorm g (ENNReal.ofReal Q) volume = (∫⁻ y, ‖g y‖ₑ ^ Q ∂volume) ^ (1 / Q) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hQ0).ne'
      ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hQ0.le]
  have heP : eLpNorm u (ENNReal.ofReal P) volume = (∫⁻ y, ‖u y‖ₑ ^ P ∂volume) ^ (1 / P) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hP0).ne'
      ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hP0.le]
  calc ‖(∫ y, g y * u y ∂volume)‖ₑ
      ≤ ∫⁻ y, ‖g y * u y‖ₑ ∂volume := enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ y, ‖g y‖ₑ * ‖u y‖ₑ ∂volume := by simp_rw [enorm_mul]
    _ ≤ (∫⁻ y, ‖g y‖ₑ ^ Q ∂volume) ^ (1 / Q) * (∫⁻ y, ‖u y‖ₑ ^ P ∂volume) ^ (1 / P) :=
        ENNReal.lintegral_mul_le_Lp_mul_Lq volume hPQ.symm hg.enorm hu.enorm
    _ = eLpNorm g (ENNReal.ofReal Q) volume * eLpNorm u (ENNReal.ofReal P) volume := by
        rw [heQ, heP]

/-- **Young's inequality, `L∞` endpoint** (for the convolution integral). For conjugate exponents
`P, Q`, the convolution value is bounded by the product of the `L^Q` norm of `η` and the `L^P` norm
of `u`, uniformly in `x`: `‖∫ η(x−y)·u(y) dy‖ ≤ ‖η‖_Q · ‖u‖_P`.  This is the **uniform boundedness**
input to the Arzelà–Ascoli step of Fréchet–Kolmogorov. -/
lemma enorm_convolutionIntegral_le {η u : ℝⁿ → ℝ} (hη : Continuous η)
    (hu : AEStronglyMeasurable u volume) {P Q : ℝ} (hPQ : P.HolderConjugate Q) (x : ℝⁿ) :
    ‖(∫ y, η (x - y) * u y ∂volume)‖ₑ
      ≤ eLpNorm η (ENNReal.ofReal Q) volume * eLpNorm u (ENNReal.ofReal P) volume := by
  have hQ0 : 0 < Q := hPQ.symm.pos
  have hP0 : 0 < P := hPQ.pos
  have heQ : eLpNorm η (ENNReal.ofReal Q) volume = (∫⁻ y, ‖η y‖ₑ ^ Q ∂volume) ^ (1 / Q) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hQ0).ne'
      ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hQ0.le]
  have heP : eLpNorm u (ENNReal.ofReal P) volume = (∫⁻ y, ‖u y‖ₑ ^ P ∂volume) ^ (1 / P) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hP0).ne'
      ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hP0.le]
  calc ‖∫ y, η (x - y) * u y ∂volume‖ₑ
      ≤ ∫⁻ y, ‖η (x - y) * u y‖ₑ ∂volume := enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ y, ‖η (x - y)‖ₑ * ‖u y‖ₑ ∂volume := by simp_rw [enorm_mul]
    _ ≤ (∫⁻ y, ‖η y‖ₑ ^ Q ∂volume) ^ (1 / Q) * (∫⁻ y, ‖u y‖ₑ ^ P ∂volume) ^ (1 / P) :=
        lintegral_enorm_mul_reflect_le hη hu hPQ x
    _ = eLpNorm η (ENNReal.ofReal Q) volume * eLpNorm u (ENNReal.ofReal P) volume := by
        rw [heQ, heP]

/-- **Equicontinuity modulus of the mollification.** The increment of the convolution between two
points `x, x'` is controlled by the `L^Q` norm of the difference of the (reflected) translates of
`η` times `‖u‖_P`: `‖(η⋆u)(x) − (η⋆u)(x')‖ ≤ ‖η(x−·) − η(x'−·)‖_Q · ‖u‖_P`.  As `x' → x` the
`η`-factor tends to `0` (`L^Q`-continuity of translation), giving equicontinuity — the second
Arzelà–Ascoli input. -/
lemma enorm_convolutionIntegral_sub_le {η u : ℝⁿ → ℝ} (hη : Continuous η)
    (hηcs : HasCompactSupport η) {P Q : ℝ} (hPQ : P.HolderConjugate Q)
    (hu : MemLp u (ENNReal.ofReal P) volume) (x x' : ℝⁿ) :
    ‖(∫ y, η (x - y) * u y ∂volume) - (∫ y, η (x' - y) * u y ∂volume)‖ₑ
      ≤ eLpNorm (fun y => η (x - y) - η (x' - y)) (ENNReal.ofReal Q) volume
        * eLpNorm u (ENNReal.ofReal P) volume := by
  have hP1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal P := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hPQ.lt.le
  have hu_li : LocallyIntegrable u volume := hu.locallyIntegrable hP1
  have hcont : ∀ z : ℝⁿ, Continuous (fun y => η (z - y)) :=
    fun z => hη.comp (continuous_const.sub continuous_id)
  have hcs : ∀ z : ℝⁿ, HasCompactSupport (fun y : ℝⁿ => η (z - y)) :=
    fun z => hηcs.comp_homeomorph (Homeomorph.subLeft z)
  have hint : ∀ z : ℝⁿ, Integrable (fun y => η (z - y) * u y) volume :=
    fun z => hu_li.integrable_smul_left_of_hasCompactSupport (hcont z) (hcs z)
  have hsub : (∫ y, η (x - y) * u y ∂volume) - (∫ y, η (x' - y) * u y ∂volume)
      = ∫ y, (η (x - y) - η (x' - y)) * u y ∂volume := by
    rw [← integral_sub (hint x) (hint x')]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    ring
  rw [hsub]
  exact enorm_integral_mul_le ((hcont x).sub (hcont x')).aestronglyMeasurable
    hu.aestronglyMeasurable hPQ

/-- **The mollification `x ↦ ∫ η(x−y)·u(y) dy` is continuous** for `η` continuous with compact
support and `u` locally integrable.  Continuity is local, so we use dominated convergence at each
point `x₀` with a bound supported on a fixed ball: for `x` near `x₀`, the integrand vanishes unless
`y` lies in a compact ball (since `η` has compact support), where `‖η(x−y)·u(y)‖ ≤ M·‖u(y)‖`.  This
packages the mollified family as continuous functions — the codomain for Arzelà–Ascoli. -/
lemma continuous_convolutionIntegral {η u : ℝⁿ → ℝ} (hη : Continuous η)
    (hηcs : HasCompactSupport η) (hu : LocallyIntegrable u volume) :
    Continuous (fun x => ∫ y, η (x - y) * u y ∂volume) := by
  obtain ⟨M, hM⟩ := hη.bounded_above_of_compact_support hηcs
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  obtain ⟨Rη, hRη⟩ := hηcs.isBounded.subset_closedBall (0 : ℝⁿ)
  rw [continuous_iff_continuousAt]
  intro x₀
  set R : ℝ := ‖x₀‖ + 1 + Rη with hRdef
  set K : Set ℝⁿ := Metric.closedBall 0 R with hKdef
  have hmeas : ∀ x : ℝⁿ, AEStronglyMeasurable (fun y => η (x - y) * u y) volume := fun x =>
    ((hη.comp (continuous_const.sub continuous_id)).aestronglyMeasurable).mul
      hu.aestronglyMeasurable
  refine continuousAt_of_dominated (bound := K.indicator (fun y => M * ‖u y‖))
    (Filter.Eventually.of_forall hmeas) ?_ ?_ ?_
  · -- domination, for `x` in the unit ball around `x₀`
    filter_upwards [Metric.ball_mem_nhds x₀ one_pos] with x hx
    filter_upwards with y
    rcases eq_or_ne (η (x - y)) 0 with h0 | h0
    · rw [h0, zero_mul, norm_zero]
      exact Set.indicator_nonneg (fun z _ => mul_nonneg hM0 (norm_nonneg _)) y
    · have hyK : y ∈ K := by
        by_contra hy
        rw [hKdef, Metric.mem_closedBall, dist_zero_right, not_le] at hy
        have hxx : ‖x‖ < ‖x₀‖ + 1 := by
          have := mem_ball_iff_norm.mp (by simpa [dist_eq_norm] using hx)
          calc ‖x‖ = ‖x - x₀ + x₀‖ := by rw [sub_add_cancel]
            _ ≤ ‖x - x₀‖ + ‖x₀‖ := norm_add_le _ _
            _ < 1 + ‖x₀‖ := by gcongr
            _ = ‖x₀‖ + 1 := by ring
        have hxy : Rη < ‖x - y‖ := by
          have : ‖y‖ - ‖x‖ ≤ ‖x - y‖ := by
            rw [← norm_neg (x - y)]; simpa [neg_sub] using norm_sub_norm_le y x
          rw [hRdef] at hy; linarith
        exact h0 (image_eq_zero_of_notMem_tsupport (fun hmem =>
          absurd (hRη hmem) (by rw [Metric.mem_closedBall, dist_zero_right, not_le]; exact hxy)))
      rw [Set.indicator_of_mem hyK, norm_mul]
      gcongr
      exact hM _
  · -- the bound is integrable
    rw [integrable_indicator_iff measurableSet_closedBall]
    exact ((hu.integrableOn_isCompact (isCompact_closedBall 0 R)).norm.const_mul M)
  · -- continuity in `x` for each fixed `y`
    filter_upwards with y
    exact ((hη.comp (continuous_id.sub continuous_const)).mul continuous_const).continuousAt

/-- **The `C⁰ → Lᵖ` embedding bound on a finite-measure domain.**  If `‖f x − g x‖ ≤ C` for
a.e. `x` in `s`, then the `Lᵖ`-distance of `f` and `g` over `s` is at most `(vol s)^{1/p}·C`.
Equivalently, the inclusion `C(K) ↪ Lᵖ(K)` is `(vol K)^{1/p}`-Lipschitz on a bounded domain `K`.
This is the bridge that transfers sup-norm precompactness (Arzelà–Ascoli) to `Lᵖ`-precompactness
(Fréchet–Kolmogorov): a uniformly small sup-distance forces a uniformly small `Lᵖ`-distance, so a
totally bounded family in `C(K)` is totally bounded in `Lᵖ(K)`. -/
lemma eLpNorm_sub_restrict_le_of_ae_bound {f g : ℝⁿ → ℝ} {s : Set ℝⁿ} {C : ℝ} {p : ℝ≥0∞}
    (hfg : ∀ᵐ x ∂(volume.restrict s), ‖f x - g x‖ ≤ C) :
    eLpNorm (fun x => f x - g x) p (volume.restrict s)
      ≤ volume s ^ p.toReal⁻¹ * ENNReal.ofReal C := by
  have h := eLpNorm_le_of_ae_bound (μ := (volume.restrict s)) (p := p) hfg
  rwa [Measure.restrict_apply_univ] at h

/-- **The `C⁰ → Lᵖ` precompactness transfer.**  On a compact space `K` with a finite measure `μ`,
the inclusion `C(K,ℝ) ↪ Lᵖ(K,μ)` (`ContinuousMap.toLp`, a *continuous linear* map) sends a compact
family of continuous functions to a compact family in `Lᵖ` — since the continuous image of a
compact set is compact.  Composed with Arzelà–Ascoli (which produces the compact family in `C(K)`
from uniform boundedness + equicontinuity), this is the topological core of Rellich–Kondrachov:
it converts `C⁰`-precompactness into `Lᵖ`-precompactness. -/
lemma isCompact_toLp_image {K : Type*} [TopologicalSpace K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K]
    {μ : Measure K} [IsFiniteMeasure μ] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {S : Set C(K, ℝ)} (hS : IsCompact S) :
    IsCompact (ContinuousMap.toLp (E := ℝ) p μ ℝ '' S) :=
  hS.image (ContinuousMap.toLp (E := ℝ) p μ ℝ).continuous

/-- **Abstract Fréchet–Kolmogorov / Rellich compactness criterion.**  Arzelà–Ascoli composed with
the `C⁰→Lᵖ` transfer (`isCompact_toLp_image`): an **equicontinuous** family `S ⊆ C(K,ℝ)` on a
compact finite-measure space `K`, whose set of underlying functions is compact for pointwise
convergence (`hS1` — pointwise relative compactness, supplied in practice by a uniform bound), is
**precompact in `Lᵖ`**.  This is the topological heart of Rellich–Kondrachov: the two analytic
hypotheses of Fréchet–Kolmogorov (uniform boundedness + uniform equicontinuity) yield
`Lᵖ`-precompactness. -/
lemma isCompact_toLp_image_of_equicontinuous {K : Type*} [TopologicalSpace K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] {μ : Measure K} [IsFiniteMeasure μ]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (S : Set C(K, ℝ))
    (hS1 : IsCompact (ContinuousMap.toFun '' S))
    (hS2 : Equicontinuous ((↑) : S → K → ℝ)) :
    IsCompact (ContinuousMap.toLp (E := ℝ) p μ ℝ '' S) :=
  (ArzelaAscoli.isCompact_of_equicontinuous S hS1 hS2).image
    (ContinuousMap.toLp (E := ℝ) p μ ℝ).continuous

/-- **Pointwise relative compactness from a uniform sup-bound.**  If every function in a family
`S ⊆ C(K,ℝ)` is bounded by a common constant `M` (`‖f x‖ ≤ M` for all `f ∈ S`, `x`), then the
closure of the set of underlying functions is compact in the topology of pointwise convergence:
all functions take values in the fixed compact box `∏ₓ [−M, M]`, which is compact by Tychonoff,
so the closure of `toFun '' S` is a closed subset of a compact set.  This supplies the pointwise
relative-compactness hypothesis (`hS1`) of the abstract Rellich criterion from the uniform
boundedness output of Young's inequality. -/
lemma isCompact_closure_toFun_image_of_bound {K : Type*} [TopologicalSpace K]
    {S : Set C(K, ℝ)} {M : ℝ} (hM : ∀ f ∈ S, ∀ x, ‖f x‖ ≤ M) :
    IsCompact (closure (ContinuousMap.toFun '' S)) := by
  set B : Set (K → ℝ) := Set.pi Set.univ (fun _ : K => Set.Icc (-M) M) with hBdef
  have hBcompact : IsCompact B := isCompact_univ_pi (fun _ => isCompact_Icc)
  have hBclosed : IsClosed B := isClosed_set_pi (fun _ _ => isClosed_Icc)
  have hsub : ContinuousMap.toFun '' S ⊆ B := by
    rintro f ⟨g, hg, rfl⟩ x -
    have hgx : |g x| ≤ M := by simpa [Real.norm_eq_abs] using hM g hg x
    exact Set.mem_Icc.mpr (abs_le.mp hgx)
  exact hBcompact.of_isClosed_subset isClosed_closure (closure_minimal hsub hBclosed)

/-- **Relative compactness in `C(K,ℝ)` (Arzelà–Ascoli, precompact form).**  An equicontinuous,
uniformly bounded family `S ⊆ C(K,ℝ)` on a compact space `K` has **compact closure** in `C(K,ℝ)`.
Unlike `isCompact_toLp_image_of_equicontinuous` (which needs `S` itself pointwise-compact), this
concludes precompactness of `S` directly: it applies Mathlib's relative-compactness Arzelà–Ascoli
(`ArzelaAscoli.isCompact_closure_of_isClosedEmbedding`) through the closed embedding
`C(K,ℝ) ↪ (K →ᵤ[compacts] ℝ)` — closed because its range is `{Continuous}`, closed in the
uniform-on-compacts topology (`UniformOnFun.isClosed_setOf_continuous`). -/
lemma isCompact_closure_of_equicontinuous_of_bound {K : Type*} [TopologicalSpace K]
    [CompactSpace K] {S : Set C(K, ℝ)} {M : ℝ}
    (hbound : ∀ f ∈ S, ∀ x, ‖f x‖ ≤ M) (heqc : Equicontinuous ((↑) : S → K → ℝ)) :
    IsCompact (closure S) := by
  have hemb : Topology.IsClosedEmbedding
      (UniformOnFun.ofFun {L : Set K | IsCompact L} ∘ ((↑) : C(K, ℝ) → (K → ℝ))) := by
    have hce : Topology.IsClosedEmbedding (ContinuousMap.toUniformOnFunIsCompact : C(K, ℝ) → _) := by
      refine ⟨ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isEmbedding, ?_⟩
      rw [ContinuousMap.range_toUniformOnFunIsCompact]
      exact UniformOnFun.isClosed_setOf_continuous CompactlyCoherentSpace.isCoherentWith
    exact hce
  refine ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
    (𝔖 := {L : Set K | IsCompact L}) (fun L hL => hL) hemb
    (fun L _ => heqc.equicontinuousOn L) (fun L _ x _ => ?_)
  exact ⟨Set.Icc (-M) M, isCompact_Icc, fun f hf =>
    Set.mem_Icc.mpr (abs_le.mp (by simpa [Real.norm_eq_abs] using hbound f hf x))⟩

/-- **Concrete `Lᵖ`-precompactness criterion (Fréchet–Kolmogorov / Rellich, precompact form).**
An equicontinuous, uniformly bounded family `S ⊆ C(K,ℝ)` on a compact finite-measure space `K` has
**compact closure in `Lᵖ`**.  Combines the relative-compactness Arzelà–Ascoli
(`isCompact_closure_of_equicontinuous_of_bound`) with the continuous-linear inclusion
`ContinuousMap.toLp`: the `C⁰`-closure of `S` is compact, its image under `toLp` is compact, and the
`Lᵖ`-closure of `toLp '' S` is a closed subset of that image.  This is the precompactness form of
the Rellich–Kondrachov compactness theorem. -/
lemma isCompact_closure_toLp_image_of_equicontinuous_of_bound {K : Type*} [TopologicalSpace K]
    [CompactSpace K] [MeasurableSpace K] [BorelSpace K] {μ : Measure K} [IsFiniteMeasure μ]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {S : Set C(K, ℝ)} {M : ℝ}
    (hbound : ∀ f ∈ S, ∀ x, ‖f x‖ ≤ M) (heqc : Equicontinuous ((↑) : S → K → ℝ)) :
    IsCompact (closure (ContinuousMap.toLp (E := ℝ) p μ ℝ '' S)) := by
  have hSc : IsCompact (closure S) := isCompact_closure_of_equicontinuous_of_bound hbound heqc
  have himg : IsCompact (ContinuousMap.toLp (E := ℝ) p μ ℝ '' closure S) :=
    hSc.image (ContinuousMap.toLp (E := ℝ) p μ ℝ).continuous
  refine himg.of_isClosed_subset isClosed_closure ?_
  exact closure_minimal (Set.image_mono subset_closure) himg.isClosed

/-- **The abstract ε/3 argument.**  In a pseudometric space, a set `S` that is, for every `ε > 0`,
contained in the `ε`-neighbourhood of *some* totally bounded set `T` (`∀ x ∈ S, ∃ y ∈ T,
dist x y < ε`) is itself totally bounded.  This is the glue of the Fréchet–Kolmogorov proof: the
original `Lᵖ` family is approximated to within `ε` by a mollified family `T` which is totally
bounded (compact closure, from `isCompact_closure_toLp_image_of_equicontinuous_of_bound`), hence
the original family is totally bounded — i.e. relatively compact in the complete space `Lᵖ`. -/
lemma totallyBounded_of_forall_approx {α : Type*} [PseudoMetricSpace α] {S : Set α}
    (h : ∀ ε > 0, ∃ T : Set α, TotallyBounded T ∧ ∀ x ∈ S, ∃ y ∈ T, dist x y < ε) :
    TotallyBounded S := by
  rw [Metric.totallyBounded_iff]
  intro ε hε
  obtain ⟨T, hT, happrox⟩ := h (ε / 2) (by positivity)
  obtain ⟨t, htfin, htsub⟩ := (Metric.totallyBounded_iff.mp hT) (ε / 2) (by positivity)
  refine ⟨t, htfin, fun x hx => ?_⟩
  obtain ⟨y, hyT, hxy⟩ := happrox x hx
  obtain ⟨z, hzt, hyz⟩ := Set.mem_iUnion₂.mp (htsub hyT)
  refine Set.mem_iUnion₂.mpr ⟨z, hzt, Metric.mem_ball.mpr ?_⟩
  calc dist x z ≤ dist x y + dist y z := dist_triangle x y z
    _ < ε / 2 + ε / 2 := add_lt_add hxy (Metric.mem_ball.mp hyz)
    _ = ε := by ring

end Sobolev

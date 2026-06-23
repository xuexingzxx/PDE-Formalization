import MyProject.Sobolev.Basic
import MyProject.Common.LpJensen
import MyProject.Common.Translation
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality

open MeasureTheory InnerProductSpace Set Topology Filter ContinuousLinearMap Module
open scoped ContDiff ENNReal NNReal

/-!
# Mollification and density of smooth functions in `W^{1,p}` (Evans §5.3)

This file builds the `Lᵖ`-mollification layer that Mathlib lacks and uses it to prove the
**Meyers–Serrin theorem** (`H = W`): smooth functions are dense in `W^{1,p}`.

The construction proceeds in layers:

* **Layer 1** — `tendsto_eLpNorm_translate_sub`: continuity of translation in `Lᵖ`,
  `‖u(· + t) − u‖_p → 0` as `t → 0`.  Proved by an `ε/3` argument: the statement is reduced
  to continuous, compactly supported functions (dense in `Lᵖ`), where it follows from uniform
  continuity together with a fixed compact bound on the support.
-/

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

namespace Sobolev

/-! ### Layer 1: continuity of translation in `Lᵖ` -/

/-- **Translation is `Lᵖ`-continuous** (`1 ≤ p < ∞`): `‖u(· + t) − u‖_p → 0` as `t → 0`.
Proved by an `ε/3` argument reducing to continuous, compactly supported functions, which are
dense in `Lᵖ`. -/
theorem tendsto_eLpNorm_translate_sub {u : ℝⁿ → ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hu : MemLp u p volume) :
    Tendsto (fun t : ℝⁿ => eLpNorm (fun x => u (x + t) - u x) p volume) (𝓝 0) (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  rcases eq_or_ne ε (⊤ : ℝ≥0∞) with rfl | hε_top
  · exact Eventually.of_forall fun t => le_top
  have h3ne : (3 : ℝ≥0∞) ≠ 0 := by norm_num
  have h3top : (3 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) := by norm_num
  have hε3 : ε / 3 ≠ 0 := ENNReal.div_ne_zero.mpr ⟨hε.ne', h3top⟩
  obtain ⟨g, hg_supp, hug, hg_cont, hg_mem⟩ :=
    hu.exists_hasCompactSupport_eLpNorm_sub_le hp hε3
  have hmid := tendsto_eLpNorm_translate_sub_continuous (p := p) hg_cont hg_supp
  rw [ENNReal.tendsto_nhds_zero] at hmid
  have hε3' : (0 : ℝ≥0∞) < ε / 3 := pos_iff_ne_zero.mpr hε3
  filter_upwards [hmid (ε / 3) hε3'] with t ht
  -- split  `u(·+t) − u  =  (u−g)∘τ  +  (g(·+t) − g)  +  (−(u−g))`,  τ = (· + t)
  have mp := measurePreserving_add_right (volume : Measure ℝⁿ) t
  have hφ_meas : AEStronglyMeasurable (u - g) volume := (hu.sub hg_mem).aestronglyMeasurable
  have hg_meas : AEStronglyMeasurable g volume := hg_cont.aestronglyMeasurable
  have hsplit : (fun x => u (x + t) - u x)
      = (u - g) ∘ (fun x => x + t) + (fun x => g (x + t) - g x) + (-(u - g)) := by
    funext x
    simp only [Function.comp_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply]
    ring
  rw [hsplit]
  have m1 : AEStronglyMeasurable ((u - g) ∘ (fun x => x + t)) volume :=
    hφ_meas.comp_measurePreserving mp
  have m2 : AEStronglyMeasurable (fun x => g (x + t) - g x) volume :=
    ((hg_cont.comp (continuous_id.add continuous_const)).aestronglyMeasurable).sub hg_meas
  have m3 : AEStronglyMeasurable (-(u - g)) volume := hφ_meas.neg
  have hT1 : eLpNorm ((u - g) ∘ (fun x => x + t)) p volume ≤ ε / 3 := by
    rw [eLpNorm_comp_measurePreserving hφ_meas mp]; exact hug
  have hT3 : eLpNorm (-(u - g)) p volume ≤ ε / 3 := by rw [eLpNorm_neg]; exact hug
  have h3 : ε / 3 + ε / 3 + ε / 3 = ε := by
    rw [ENNReal.div_add_div_same, ENNReal.div_add_div_same, show ε + ε + ε = ε * 3 by ring]
    exact ENNReal.mul_div_cancel_right h3ne h3top
  calc eLpNorm ((u - g) ∘ (fun x => x + t) + (fun x => g (x + t) - g x) + (-(u - g))) p volume
      ≤ eLpNorm ((u - g) ∘ (fun x => x + t) + (fun x => g (x + t) - g x)) p volume
          + eLpNorm (-(u - g)) p volume := eLpNorm_add_le (m1.add m2) m3 Fact.out
    _ ≤ (eLpNorm ((u - g) ∘ (fun x => x + t)) p volume
          + eLpNorm (fun x => g (x + t) - g x) p volume) + eLpNorm (-(u - g)) p volume := by
        gcongr; exact eLpNorm_add_le m1 m2 Fact.out
    _ ≤ ε / 3 + ε / 3 + ε / 3 := by gcongr
    _ = ε := h3

/-! ### Layer 2: `Lᵖ`-convergence of mollification -/

open scoped Convolution

/-- **Key mollification estimate.** For a nonnegative, continuous, compactly supported
mollifier `η` with `∫ η = 1`, the `Lᵖ` error of `η ⋆ u` is controlled by an `η`-average of the
translation moduli of `u`:
`‖η ⋆ u − u‖_p^p ≤ ∫ η(y) · ‖u(· − y) − u‖_p^p dy`.
Proof: write `(η⋆u)(x) − u(x) = ∫ η(y)(u(x−y) − u(x)) dy` (as `∫ η = 1`), apply the triangle
inequality and the weighted Jensen inequality pointwise, then integrate in `x` and use Tonelli. -/
lemma eLpNorm_convolution_sub_rpow_le {η : ℝⁿ → ℝ} (hη_cont : Continuous η)
    (hη_supp : HasCompactSupport η) (hη_nonneg : ∀ y, 0 ≤ η y) (hη_int : ∫ y, η y = 1)
    {u : ℝⁿ → ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hu : MemLp u p volume) :
    (eLpNorm (fun x => (η ⋆[lsmul ℝ ℝ, volume] u) x - u x) p volume) ^ p.toReal
      ≤ ∫⁻ y, ENNReal.ofReal (η y) *
          (eLpNorm (fun x => u (x - y) - u x) p volume) ^ p.toReal ∂volume := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hp0 : p ≠ 0 := fun h => by simp [h] at hp1
  have hP1 : 1 ≤ p.toReal := by
    rw [show (1 : ℝ) = (1 : ℝ≥0∞).toReal from ENNReal.toReal_one.symm]
    exact ENNReal.toReal_mono hp hp1
  have hP0 : 0 < p.toReal := lt_of_lt_of_le one_pos hP1
  have hμ : AEStronglyMeasurable u volume := hu.aestronglyMeasurable
  have hη_intble : Integrable η volume := hη_cont.integrable_of_hasCompactSupport hη_supp
  have hu_li : LocallyIntegrable u volume := hu.locallyIntegrable hp1
  have hconv : ConvolutionExists η u (lsmul ℝ ℝ) volume :=
    hη_supp.convolutionExists_left (L := lsmul ℝ ℝ) hη_cont hu_li
  have hw_top : ∀ y, ENNReal.ofReal (η y) ≠ ⊤ := fun _ => ENNReal.ofReal_ne_top
  have hw_meas : AEMeasurable (fun y => ENNReal.ofReal (η y)) volume :=
    (ENNReal.measurable_ofReal.comp hη_cont.measurable).aemeasurable
  have hw1 : ∫⁻ y, ENNReal.ofReal (η y) ∂volume = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hη_intble (Eventually.of_forall hη_nonneg), hη_int,
      ENNReal.ofReal_one]
  -- pointwise rewrite of the convolution difference
  have hpt : ∀ x, (η ⋆[lsmul ℝ ℝ, volume] u) x - u x
      = ∫ y, η y * (u (x - y) - u x) ∂volume := by
    intro x
    have huc : Integrable (fun y => η y * u (x - y)) volume := by
      have h := hconv x
      simpa only [ConvolutionExistsAt, lsmul_apply, smul_eq_mul] using h
    have hcc : Integrable (fun y => η y * u x) volume := hη_intble.mul_const (u x)
    have hconv_eq : (η ⋆[lsmul ℝ ℝ, volume] u) x = ∫ y, η y * u (x - y) ∂volume := by
      simp_rw [convolution_def, lsmul_apply, smul_eq_mul]
    have hux : (∫ y, η y * u x ∂volume) = u x := by rw [integral_mul_const, hη_int, one_mul]
    calc (η ⋆[lsmul ℝ ℝ, volume] u) x - u x
        = (∫ y, η y * u (x - y) ∂volume) - ∫ y, η y * u x ∂volume := by rw [hconv_eq, hux]
      _ = ∫ y, (η y * u (x - y) - η y * u x) ∂volume := (integral_sub huc hcc).symm
      _ = ∫ y, η y * (u (x - y) - u x) ∂volume := by
          refine integral_congr_ae (Eventually.of_forall fun y => ?_); ring
  -- pointwise `enorm`-power bound via triangle + weighted Jensen
  have hbound : ∀ x, ‖(η ⋆[lsmul ℝ ℝ, volume] u) x - u x‖ₑ ^ p.toReal
      ≤ ∫⁻ y, ENNReal.ofReal (η y) * ‖u (x - y) - u x‖ₑ ^ p.toReal ∂volume := by
    intro x
    have htri : ‖(η ⋆[lsmul ℝ ℝ, volume] u) x - u x‖ₑ
        ≤ ∫⁻ y, ENNReal.ofReal (η y) * ‖u (x - y) - u x‖ₑ ∂volume := by
      rw [hpt x]
      refine (enorm_integral_le_lintegral_enorm _).trans_eq (lintegral_congr fun y => ?_)
      rw [enorm_mul, Real.enorm_eq_ofReal (hη_nonneg y)]
    have hhmeas : AEMeasurable (fun y => ‖u (x - y) - u x‖ₑ) volume :=
      ((hμ.comp_quasiMeasurePreserving
        (quasiMeasurePreserving_sub_left_of_right_invariant volume x)).sub
        aestronglyMeasurable_const).enorm
    calc ‖(η ⋆[lsmul ℝ ℝ, volume] u) x - u x‖ₑ ^ p.toReal
        ≤ (∫⁻ y, ENNReal.ofReal (η y) * ‖u (x - y) - u x‖ₑ ∂volume) ^ p.toReal :=
          ENNReal.rpow_le_rpow htri hP0.le
      _ ≤ ∫⁻ y, ENNReal.ofReal (η y) * ‖u (x - y) - u x‖ₑ ^ p.toReal ∂volume :=
          rpow_lintegral_weighted_le hw_meas hhmeas hw_top hw1 hP1
  -- joint measurability for Tonelli
  have hΦ : MeasurePreserving (fun z : ℝⁿ × ℝⁿ => (z.1 - z.2, z.2))
      (volume.prod volume) (volume.prod volume) := measurePreserving_sub_prod volume volume
  have husub : AEStronglyMeasurable (fun q : ℝⁿ × ℝⁿ => u (q.1 - q.2)) (volume.prod volume) :=
    hμ.comp_fst.comp_measurePreserving hΦ
  have hjoint : AEMeasurable (fun q : ℝⁿ × ℝⁿ =>
      ENNReal.ofReal (η q.2) * ‖u (q.1 - q.2) - u q.1‖ₑ ^ p.toReal) (volume.prod volume) :=
    ((ENNReal.measurable_ofReal.comp
        (hη_cont.measurable.comp measurable_snd)).aemeasurable).mul
      ((ENNReal.continuous_rpow_const (y := p.toReal)).measurable.comp_aemeasurable
        (husub.sub hμ.comp_fst).enorm)
  -- assemble: integrate, swap, identify
  have hLHS : (eLpNorm (fun x => (η ⋆[lsmul ℝ ℝ, volume] u) x - u x) p volume) ^ p.toReal
      = ∫⁻ x, ‖(η ⋆[lsmul ℝ ℝ, volume] u) x - u x‖ₑ ^ p.toReal ∂volume := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp, ← ENNReal.rpow_mul, one_div,
      inv_mul_cancel₀ hP0.ne', ENNReal.rpow_one]
  rw [hLHS]
  calc ∫⁻ x, ‖(η ⋆[lsmul ℝ ℝ, volume] u) x - u x‖ₑ ^ p.toReal ∂volume
      ≤ ∫⁻ x, ∫⁻ y, ENNReal.ofReal (η y) * ‖u (x - y) - u x‖ₑ ^ p.toReal ∂volume ∂volume :=
        lintegral_mono hbound
    _ = ∫⁻ y, ∫⁻ x, ENNReal.ofReal (η y) * ‖u (x - y) - u x‖ₑ ^ p.toReal ∂volume ∂volume :=
        lintegral_lintegral_swap hjoint
    _ = ∫⁻ y, ENNReal.ofReal (η y) *
          (eLpNorm (fun x => u (x - y) - u x) p volume) ^ p.toReal ∂volume := by
        refine lintegral_congr fun y => ?_
        have hmy : AEMeasurable (fun x => ‖u (x - y) - u x‖ₑ ^ p.toReal) volume :=
          (ENNReal.continuous_rpow_const (y := p.toReal)).measurable.comp_aemeasurable
            ((hμ.comp_quasiMeasurePreserving
              (measurePreserving_sub_right volume y).quasiMeasurePreserving).sub hμ).enorm
        rw [lintegral_const_mul'' _ hmy,
          eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp, ← ENNReal.rpow_mul, one_div,
          inv_mul_cancel₀ hP0.ne', ENNReal.rpow_one]

/-- **Uniform mollification bound** (the approximation step of Fréchet–Kolmogorov).  If the `Lᵖ`
translation modulus of `u` is `≤ ε` at every `y` where the (normalized, nonnegative, compactly
supported) mollifier `η` is nonzero, then `‖η⋆u − u‖_p ≤ ε`.  Since `ε` does not depend on `u`,
this is **uniform** over any family sharing the modulus bound.  Reduces to the key estimate:
`‖η⋆u−u‖_p^p ≤ ∫η(y)‖u(·−y)−u‖_p^p ≤ ε^p ∫η = ε^p`. -/
lemma eLpNorm_convolution_sub_le_of_modulus {η : ℝⁿ → ℝ} (hη_cont : Continuous η)
    (hη_supp : HasCompactSupport η) (hη_nonneg : ∀ y, 0 ≤ η y) (hη_int : ∫ y, η y = 1)
    {u : ℝⁿ → ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hu : MemLp u p volume) {ε : ℝ≥0∞}
    (hmod : ∀ y, η y ≠ 0 → eLpNorm (fun x => u (x - y) - u x) p volume ≤ ε) :
    eLpNorm (fun x => (η ⋆[lsmul ℝ ℝ, volume] u) x - u x) p volume ≤ ε := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hp0 : p ≠ 0 := fun h => by simp [h] at hp1
  have hP0 : 0 < p.toReal := by
    have h1 : (1 : ℝ) ≤ p.toReal := by
      rw [show (1 : ℝ) = (1 : ℝ≥0∞).toReal from ENNReal.toReal_one.symm]
      exact ENNReal.toReal_mono hp hp1
    linarith
  have hη_intble : Integrable η volume := hη_cont.integrable_of_hasCompactSupport hη_supp
  have hw1 : ∫⁻ y, ENNReal.ofReal (η y) ∂volume = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hη_intble (Eventually.of_forall hη_nonneg), hη_int,
      ENNReal.ofReal_one]
  have hwmeas : Measurable (fun y => ENNReal.ofReal (η y)) :=
    ENNReal.measurable_ofReal.comp hη_cont.measurable
  have key := eLpNorm_convolution_sub_rpow_le hη_cont hη_supp hη_nonneg hη_int hp hu
  have hbd : ∫⁻ y, ENNReal.ofReal (η y)
        * (eLpNorm (fun x => u (x - y) - u x) p volume) ^ p.toReal ∂volume ≤ ε ^ p.toReal := by
    calc ∫⁻ y, ENNReal.ofReal (η y)
          * (eLpNorm (fun x => u (x - y) - u x) p volume) ^ p.toReal ∂volume
        ≤ ∫⁻ y, ENNReal.ofReal (η y) * ε ^ p.toReal ∂volume := by
          refine lintegral_mono fun y => ?_
          rcases eq_or_ne (η y) 0 with h | h
          · simp [h]
          · exact mul_le_mul' le_rfl (ENNReal.rpow_le_rpow (hmod y h) hP0.le)
      _ = (∫⁻ y, ENNReal.ofReal (η y) ∂volume) * ε ^ p.toReal := by
          rw [lintegral_mul_const _ hwmeas]
      _ = ε ^ p.toReal := by rw [hw1, one_mul]
  have hpow : (eLpNorm (fun x => (η ⋆[lsmul ℝ ℝ, volume] u) x - u x) p volume)
      ^ p.toReal ≤ ε ^ p.toReal := key.trans hbd
  have hroot := ENNReal.rpow_le_rpow hpow (by positivity : (0 : ℝ) ≤ 1 / p.toReal)
  rwa [← ENNReal.rpow_mul, ← ENNReal.rpow_mul, mul_one_div, div_self hP0.ne',
    ENNReal.rpow_one, ENNReal.rpow_one] at hroot

/-- **Convolution as the reflected integral**: `(η ⋆ u) x = ∫ η(x − y)·u(y) dy`.  Mathlib's
convolution is `∫ η(t)·u(x − t) dt`; substituting the measure-preserving reflection `t ↦ x − t`
gives the form used by the Fréchet–Kolmogorov dischargers. -/
lemma convolution_eq_integral_sub {η u : ℝⁿ → ℝ} (x : ℝⁿ) :
    (η ⋆[lsmul ℝ ℝ, volume] u) x = ∫ y, η (x - y) * u y ∂volume := by
  have hmp : MeasurePreserving (fun y : ℝⁿ => x - y) volume volume := by
    have hneg : MeasurePreserving (fun y : ℝⁿ => -y) volume volume := by
      refine ⟨measurable_neg, ?_⟩
      have h1 : (fun y : ℝⁿ => -y) = fun y => (-1 : ℝ) • y := by funext y; rw [neg_one_smul]
      rw [h1, Measure.map_addHaar_smul volume (show (-1 : ℝ) ≠ 0 by norm_num)]; simp
    have hcomp := hneg.comp (measurePreserving_sub_right volume x)
    have hfun : (fun y : ℝⁿ => -y) ∘ (fun y => y - x) = fun y => x - y := by funext y; simp [neg_sub]
    rwa [hfun] at hcomp
  rw [convolution_def]
  simp_rw [lsmul_apply, smul_eq_mul]
  have he : MeasurableEmbedding (fun y : ℝⁿ => x - y) :=
    (Homeomorph.subLeft x).measurableEmbedding
  rw [← hmp.integral_comp he (fun z => η z * u (x - z))]
  simp only [sub_sub_cancel]

/-- **Uniform mollification bound, integral form** (matching the Fréchet–Kolmogorov dischargers).
If the `Lᵖ` translation modulus of `u` is `≤ ε` wherever `η` is nonzero, then
`‖(∫ η(·−y)·u(y) dy) − u‖_p ≤ ε`.  The bridge `convolution_eq_integral_sub` plus
`eLpNorm_convolution_sub_le_of_modulus`. -/
lemma eLpNorm_integral_convolution_sub_le_of_modulus {η : ℝⁿ → ℝ} (hη_cont : Continuous η)
    (hη_supp : HasCompactSupport η) (hη_nonneg : ∀ y, 0 ≤ η y) (hη_int : ∫ y, η y = 1)
    {u : ℝⁿ → ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hu : MemLp u p volume) {ε : ℝ≥0∞}
    (hmod : ∀ y, η y ≠ 0 → eLpNorm (fun x => u (x - y) - u x) p volume ≤ ε) :
    eLpNorm (fun x => (∫ y, η (x - y) * u y ∂volume) - u x) p volume ≤ ε := by
  have hbridge : (fun x => (∫ y, η (x - y) * u y ∂volume) - u x)
      = (fun x => (η ⋆[lsmul ℝ ℝ, volume] u) x - u x) := by
    funext x; rw [convolution_eq_integral_sub]
  rw [hbridge]
  exact eLpNorm_convolution_sub_le_of_modulus hη_cont hη_supp hη_nonneg hη_int hp hu hmod

/-- **Mollification converges in `Lᵖ`** (`1 ≤ p < ∞`): for a sequence of normalized bump
mollifiers whose outer radius tends to `0`, the mollifications `η ⋆ u` converge to `u` in `Lᵖ`.
Combines the key estimate with the `Lᵖ`-continuity of translation. -/
theorem tendsto_eLpNorm_convolution_sub {u : ℝⁿ → ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (hu : MemLp u p volume) {ι : Type*} {l : Filter ι} {φ : ι → ContDiffBump (0 : ℝⁿ)}
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0)) :
    Tendsto (fun i => eLpNorm
      (fun x => ((φ i).normed volume ⋆[lsmul ℝ ℝ, volume] u) x - u x) p volume) l (𝓝 0) := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hp0 : p ≠ 0 := fun h => by simp [h] at hp1
  have hP1 : 1 ≤ p.toReal := by
    rw [show (1 : ℝ) = (1 : ℝ≥0∞).toReal from ENNReal.toReal_one.symm]
    exact ENNReal.toReal_mono hp hp1
  have hP0 : 0 < p.toReal := lt_of_lt_of_le one_pos hP1
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  rcases eq_or_ne ε ⊤ with rfl | hε_top
  · exact Eventually.of_forall fun i => le_top
  -- Layer 1 supplies a radius `δ` controlling the translation modulus
  have hL1 := tendsto_eLpNorm_translate_sub hp hu
  rw [ENNReal.tendsto_nhds_zero] at hL1
  obtain ⟨δ, hδ0, hδ⟩ : ∃ δ > 0, ∀ y : ℝⁿ, ‖y‖ < δ →
      eLpNorm (fun x => u (x - y) - u x) p volume ≤ ε := by
    obtain ⟨δ, hδ0, hδ⟩ := Metric.eventually_nhds_iff.mp (hL1 ε hε)
    refine ⟨δ, hδ0, fun y hy => ?_⟩
    exact hδ (y := -y) (by rw [dist_eq_norm, sub_zero, norm_neg]; exact hy)
  filter_upwards [hφ.eventually (Iio_mem_nhds hδ0)] with i hi
  have hηcont : Continuous ((φ i).normed volume) := ((φ i).contDiff_normed (n := 1)).continuous
  have hηsupp : HasCompactSupport ((φ i).normed volume) := (φ i).hasCompactSupport_normed
  have hw_meas : AEMeasurable (fun y => ENNReal.ofReal ((φ i).normed volume y)) volume :=
    (ENNReal.measurable_ofReal.comp hηcont.measurable).aemeasurable
  have hw1 : ∫⁻ y, ENNReal.ofReal ((φ i).normed volume y) ∂volume = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hηcont.integrable_of_hasCompactSupport hηsupp)
      (Eventually.of_forall (φ i).nonneg_normed), (φ i).integral_normed, ENNReal.ofReal_one]
  -- bound the key-estimate right-hand side by `ε ^ p.toReal`
  have hbound : ∫⁻ y, ENNReal.ofReal ((φ i).normed volume y) *
      (eLpNorm (fun x => u (x - y) - u x) p volume) ^ p.toReal ∂volume ≤ ε ^ p.toReal := by
    have hle : ∀ y, ENNReal.ofReal ((φ i).normed volume y)
          * (eLpNorm (fun x => u (x - y) - u x) p volume) ^ p.toReal
        ≤ ε ^ p.toReal * ENNReal.ofReal ((φ i).normed volume y) := by
      intro y
      rcases eq_or_ne ((φ i).normed volume y) 0 with h0 | h0
      · simp [h0]
      · have hyb : y ∈ Metric.ball (0 : ℝⁿ) (φ i).rOut := by
          rw [← (φ i).support_normed_eq (μ := volume)]; exact h0
        have hyδ : ‖y‖ < δ := lt_trans (mem_ball_zero_iff.mp hyb) hi
        rw [mul_comm]
        gcongr
        exact hδ y hyδ
    calc ∫⁻ y, ENNReal.ofReal ((φ i).normed volume y)
            * (eLpNorm (fun x => u (x - y) - u x) p volume) ^ p.toReal ∂volume
        ≤ ∫⁻ y, ε ^ p.toReal * ENNReal.ofReal ((φ i).normed volume y) ∂volume := lintegral_mono hle
      _ = ε ^ p.toReal * ∫⁻ y, ENNReal.ofReal ((φ i).normed volume y) ∂volume :=
          lintegral_const_mul'' _ hw_meas
      _ = ε ^ p.toReal := by rw [hw1, mul_one]
  have hkey := eLpNorm_convolution_sub_rpow_le hηcont hηsupp (φ i).nonneg_normed
    (φ i).integral_normed hp hu
  have hfin : (eLpNorm (fun x => ((φ i).normed volume ⋆[lsmul ℝ ℝ, volume] u) x - u x) p volume)
      ^ p.toReal ≤ ε ^ p.toReal := le_trans hkey hbound
  calc eLpNorm (fun x => ((φ i).normed volume ⋆[lsmul ℝ ℝ, volume] u) x - u x) p volume
      = ((eLpNorm (fun x => ((φ i).normed volume ⋆[lsmul ℝ ℝ, volume] u) x - u x) p volume)
          ^ p.toReal) ^ (1 / p.toReal) := by
        rw [← ENNReal.rpow_mul, mul_one_div, div_self hP0.ne', ENNReal.rpow_one]
    _ ≤ (ε ^ p.toReal) ^ (1 / p.toReal) := ENNReal.rpow_le_rpow hfin (by positivity)
    _ = ε := by rw [← ENNReal.rpow_mul, mul_one_div, div_self hP0.ne', ENNReal.rpow_one]

/-! ### Layer 3: the regularization (commutation) identity -/

/-- **The derivative passes through the convolution onto the weak derivative.** If `v` is the
weak derivative of `u` in direction `e`, then for a smooth, compactly supported mollifier `η`,
`(∂ₑη) ⋆ u = η ⋆ v`.  Proved by applying the weak-derivative identity to the reflected test
function `z ↦ η(x − z)` (whose directional derivative is `−(∂ₑη)(x − z)`). -/
lemma convolution_deriv_eq {η : ℝⁿ → ℝ} (hη : ContDiff ℝ ∞ η) (hηsupp : HasCompactSupport η)
    {u v : ℝⁿ → ℝ} (e : ℝⁿ) (hweak : IsWeakDerivInDir univ e u v) (x : ℝⁿ) :
    ((fun z => fderiv ℝ η z e) ⋆[lsmul ℝ ℝ, volume] u) x
      = (η ⋆[lsmul ℝ ℝ, volume] v) x := by
  set φ : ℝⁿ → ℝ := fun z => η (x - z) with hφdef
  have hφ_cd : ContDiff ℝ ∞ φ := hη.comp (contDiff_const.sub contDiff_id)
  have hφ_cs : HasCompactSupport φ := hηsupp.comp_homeomorph (Homeomorph.subLeft x)
  have hφ_test : IsTestFunction univ φ := ⟨hφ_cd, hφ_cs, subset_univ _⟩
  have hchain : ∀ z, fderiv ℝ φ z e = - fderiv ℝ η (x - z) e := by
    intro z
    have hg : HasFDerivAt (fun z : ℝⁿ => x - z) (-ContinuousLinearMap.id ℝ ℝⁿ) z :=
      (hasFDerivAt_id z).const_sub x
    have hηd : HasFDerivAt η (fderiv ℝ η (x - z)) (x - z) :=
      (hη.differentiable (by simp)).differentiableAt.hasFDerivAt
    have hcomp : HasFDerivAt φ ((fderiv ℝ η (x - z)).comp (-ContinuousLinearMap.id ℝ ℝⁿ)) z :=
      hηd.comp z hg
    rw [hcomp.fderiv]
    simp
  rw [convolution_eq_swap, convolution_eq_swap]
  simp only [lsmul_apply, smul_eq_mul]
  have hw := hweak φ hφ_test
  calc ∫ t, fderiv ℝ η (x - t) e * u t ∂volume
      = ∫ t, u t * fderiv ℝ η (x - t) e ∂volume :=
        integral_congr_ae (Eventually.of_forall fun t => mul_comm _ _)
    _ = -∫ t, u t * fderiv ℝ φ t e ∂volume := by
        simp_rw [hchain, mul_neg, integral_neg, neg_neg]
    _ = - -∫ t, v t * φ t ∂volume := by rw [hw]
    _ = ∫ t, η (x - t) * v t ∂volume := by
        rw [neg_neg]
        refine integral_congr_ae (Eventually.of_forall fun t => ?_)
        change v t * φ t = η (x - t) * v t
        simp only [hφdef]; ring

/-! ### Layer 3 (Route A): the regularization weak-derivative relation via Fubini -/

/-- Integrability of the Fubini integrand `η(t)·w(x−t)·ξ(x)` over the product measure, for `η, ξ`
continuous with compact support and `w` locally integrable.  Proved by truncating `w` to a ball
(so `Integrable.convolution_integrand` applies) and multiplying by the bounded factor `ξ`. -/
lemma integrable_convolution_integrand_mul {η ξ w : ℝⁿ → ℝ}
    (hη_cont : Continuous η) (hη_supp : HasCompactSupport η)
    (hξ_cont : Continuous ξ) (hξ_supp : HasCompactSupport ξ) (hw : LocallyIntegrable w volume) :
    Integrable (fun p : ℝⁿ × ℝⁿ => η p.2 * w (p.1 - p.2) * ξ p.1) (volume.prod volume) := by
  have hη_int : Integrable η volume := hη_cont.integrable_of_hasCompactSupport hη_supp
  obtain ⟨Rξ, hRξ⟩ := (IsCompact.isBounded hξ_supp).subset_closedBall (0 : ℝⁿ)
  obtain ⟨Rη, hRη⟩ := (IsCompact.isBounded hη_supp).subset_closedBall (0 : ℝⁿ)
  set R : ℝ := Rξ + Rη with hRdef
  have hw'_int : Integrable ((Metric.closedBall (0 : ℝⁿ) R).indicator w) volume :=
    (integrable_indicator_iff measurableSet_closedBall).mpr
      (hw.integrableOn_isCompact (isCompact_closedBall 0 R))
  have hFeq : (fun p : ℝⁿ × ℝⁿ => η p.2 * w (p.1 - p.2) * ξ p.1)
      = fun p => η p.2 * (Metric.closedBall (0 : ℝⁿ) R).indicator w (p.1 - p.2) * ξ p.1 := by
    funext p
    rcases eq_or_ne (η p.2) 0 with h | h
    · simp [h]
    rcases eq_or_ne (ξ p.1) 0 with h' | h'
    · simp [h']
    have hmem : p.1 - p.2 ∈ Metric.closedBall (0 : ℝⁿ) R := by
      have h1 := hRξ (subset_tsupport _ h')
      have h2 := hRη (subset_tsupport _ h)
      rw [Metric.mem_closedBall, dist_zero_right] at h1 h2 ⊢
      calc ‖p.1 - p.2‖ ≤ ‖p.1‖ + ‖p.2‖ := norm_sub_le _ _
        _ ≤ R := add_le_add h1 h2
    rw [Set.indicator_of_mem hmem]
  rw [hFeq]
  have hconv : Integrable
      (fun p : ℝⁿ × ℝⁿ => η p.2 * (Metric.closedBall (0 : ℝⁿ) R).indicator w (p.1 - p.2))
      (volume.prod volume) := by
    have := hη_int.convolution_integrand (L := lsmul ℝ ℝ) hw'_int
    simpa only [lsmul_apply, smul_eq_mul] using this
  obtain ⟨C, hC⟩ := hξ_cont.bounded_above_of_compact_support hξ_supp
  have hgrp : (fun p : ℝⁿ × ℝⁿ =>
        η p.2 * (Metric.closedBall (0 : ℝⁿ) R).indicator w (p.1 - p.2) * ξ p.1)
      = fun p => (η p.2 * (Metric.closedBall (0 : ℝⁿ) R).indicator w (p.1 - p.2)) * ξ p.1 := by
    funext p; ring
  rw [hgrp]
  exact hconv.mul_bdd (hξ_cont.comp continuous_fst).aestronglyMeasurable
    (Eventually.of_forall fun p => hC p.1)

/-- **The mollification `η ⋆ u` has weak derivative `η ⋆ v`** (in direction `e`) whenever `v`
is the weak derivative of `u`. Proved directly from the definition by Fubini: pairing against a
test function `ψ`, swap the order of integration, translate, and apply the weak-derivative
identity of `u` against the translated test function `ψ(· + t)`. -/
lemma isWeakDerivInDir_convolution {η : ℝⁿ → ℝ} (hη_cd : ContDiff ℝ ∞ η)
    (hη_supp : HasCompactSupport η) {u v : ℝⁿ → ℝ} (hu : LocallyIntegrable u volume)
    (hv : LocallyIntegrable v volume) (e : ℝⁿ) (hweak : IsWeakDerivInDir univ e u v) :
    IsWeakDerivInDir univ e (η ⋆[lsmul ℝ ℝ, volume] u) (η ⋆[lsmul ℝ ℝ, volume] v) := by
  have hη_cont : Continuous η := hη_cd.continuous
  intro ψ hψ
  have hDψ_cont : Continuous (fun x => fderiv ℝ ψ x e) := hψ.continuous_dirDeriv e
  have hDψ_supp : HasCompactSupport (fun x => fderiv ℝ ψ x e) := hψ.hasCompactSupport_dirDeriv e
  have hψ_cont : Continuous ψ := hψ.contDiff.continuous
  -- for each `t`, the translated test function `ψ(· + t)`
  have htest : ∀ t : ℝⁿ, IsTestFunction univ (fun x => ψ (x + t)) := by
    intro t
    refine ⟨hψ.contDiff.comp (contDiff_id.add contDiff_const), ?_, subset_univ _⟩
    exact hψ.hasCompactSupport.comp_homeomorph (Homeomorph.addRight t)
  -- the chain rule: `fderiv ℝ ψ (x + t) e = fderiv ℝ (ψ(· + t)) x e`
  have hchain : ∀ t x : ℝⁿ, fderiv ℝ (fun y => ψ (y + t)) x e = fderiv ℝ ψ (x + t) e := by
    intro t x
    have hg : HasFDerivAt (fun y : ℝⁿ => y + t) (ContinuousLinearMap.id ℝ ℝⁿ) x := by
      simpa using (hasFDerivAt_id x).add_const t
    have hψd : HasFDerivAt ψ (fderiv ℝ ψ (x + t)) (x + t) :=
      (hψ.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
    have hcomp : HasFDerivAt (fun y => ψ (y + t))
        ((fderiv ℝ ψ (x + t)).comp (ContinuousLinearMap.id ℝ ℝⁿ)) x := hψd.comp x hg
    rw [hcomp.fderiv]; simp
  -- weak-derivative identity for `u` against `ψ(· + t)`, after translating
  have hinner : ∀ t : ℝⁿ, (∫ x, u (x - t) * fderiv ℝ ψ x e ∂volume)
      = -∫ x, v (x - t) * ψ x ∂volume := by
    intro t
    have hL : (∫ x, u (x - t) * fderiv ℝ ψ x e ∂volume)
        = ∫ x, u x * fderiv ℝ (fun y => ψ (y + t)) x e ∂volume := by
      rw [← integral_add_left_eq_self (fun x => u (x - t) * fderiv ℝ ψ x e) t]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [add_sub_cancel_left]
      rw [hchain, add_comm t x]
    have hR : (∫ x, v (x - t) * ψ x ∂volume) = ∫ x, v x * ψ (x + t) ∂volume := by
      rw [← integral_add_left_eq_self (fun x => v (x - t) * ψ x) t]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [add_sub_cancel_left]
      rw [add_comm t x]
    rw [hL, hweak _ (htest t), hR]
  -- pairing identity: `∫ (η⋆w)·ξ = ∫ₜ η(t) · ∫ₓ w(x−t)·ξ(x)` (convolution_def + Fubini)
  have hpair : ∀ (w ξ : ℝⁿ → ℝ),
      Integrable (fun p : ℝⁿ × ℝⁿ => η p.2 * w (p.1 - p.2) * ξ p.1) (volume.prod volume) →
      (∫ x, (η ⋆[lsmul ℝ ℝ, volume] w) x * ξ x ∂volume)
        = ∫ t, η t * (∫ x, w (x - t) * ξ x ∂volume) ∂volume := by
    intro w ξ hF
    calc ∫ x, (η ⋆[lsmul ℝ ℝ, volume] w) x * ξ x ∂volume
        = ∫ x, ∫ t, η t * w (x - t) * ξ x ∂volume ∂volume := by
          simp_rw [convolution_def, lsmul_apply, smul_eq_mul, ← integral_mul_const]
      _ = ∫ t, ∫ x, η t * w (x - t) * ξ x ∂volume ∂volume := integral_integral_swap hF
      _ = ∫ t, η t * (∫ x, w (x - t) * ξ x ∂volume) ∂volume := by
          refine integral_congr_ae (Eventually.of_forall fun t => ?_)
          simp only []
          rw [show (fun x => η t * w (x - t) * ξ x) = fun x => η t * (w (x - t) * ξ x) from by
            funext x; ring, integral_const_mul]
  rw [hpair u (fun x => fderiv ℝ ψ x e)
        (integrable_convolution_integrand_mul hη_cont hη_supp hDψ_cont hDψ_supp hu),
      hpair v ψ
        (integrable_convolution_integrand_mul hη_cont hη_supp hψ_cont hψ.hasCompactSupport hv)]
  simp_rw [hinner, mul_neg, integral_neg]

/-! ### Layer 4: the Meyers–Serrin density theorem -/

/-- **Meyers–Serrin (`H = W`), one-direction core.** If `v` is the weak derivative of `u` in
direction `e` and both lie in `Lᵖ` (`1 ≤ p < ∞`), then `u` and `v` are *simultaneously*
approximated in `Lᵖ` by a smooth function `w` together with its weak derivative `w'`: take
`w = η_δ ⋆ u` for a bump `η_δ` of small enough radius, which is `C^∞`, has weak derivative
`η_δ ⋆ v`, and converges to `u` (resp. `v`) in `Lᵖ`. -/
theorem exists_contDiff_isWeakDerivInDir_eLpNorm_le {u v : ℝⁿ → ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hu : MemLp u p volume) (hv : MemLp v p volume) (e : ℝⁿ)
    (hweak : IsWeakDerivInDir univ e u v) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ w w' : ℝⁿ → ℝ, ContDiff ℝ ∞ w ∧ IsWeakDerivInDir univ e w w' ∧
      eLpNorm (u - w) p volume ≤ ε ∧ eLpNorm (v - w') p volume ≤ ε := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hu_li : LocallyIntegrable u volume := hu.locallyIntegrable hp1
  have hv_li : LocallyIntegrable v volume := hv.locallyIntegrable hp1
  -- a sequence of bump functions whose outer radius shrinks to `0`
  set φ : ℕ → ContDiffBump (0 : ℝⁿ) := fun k =>
    ⟨1 / (k + 2 : ℝ), 1 / (k + 1 : ℝ), by positivity,
      one_div_lt_one_div_of_lt (by positivity) (by linarith)⟩ with hφdef
  have hφ : Tendsto (fun k => (φ k).rOut) atTop (𝓝 0) := by
    simpa [hφdef] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hcu := tendsto_eLpNorm_convolution_sub hp hu hφ
  have hcv := tendsto_eLpNorm_convolution_sub hp hv hφ
  rw [ENNReal.tendsto_nhds_zero] at hcu hcv
  obtain ⟨k, hku, hkv⟩ := ((hcu ε hε).and (hcv ε hε)).exists
  refine ⟨(φ k).normed volume ⋆[lsmul ℝ ℝ, volume] u,
          (φ k).normed volume ⋆[lsmul ℝ ℝ, volume] v, ?_, ?_, ?_, ?_⟩
  · exact (φ k).hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
      (φ k).contDiff_normed hu_li
  · exact isWeakDerivInDir_convolution (φ k).contDiff_normed (φ k).hasCompactSupport_normed
      hu_li hv_li e hweak
  · rw [show u - ((φ k).normed volume ⋆[lsmul ℝ ℝ, volume] u)
        = -fun x => ((φ k).normed volume ⋆[lsmul ℝ ℝ, volume] u) x - u x from by
          funext x; simp only [Pi.sub_apply, Pi.neg_apply]; ring, eLpNorm_neg]
    exact hku
  · rw [show v - ((φ k).normed volume ⋆[lsmul ℝ ℝ, volume] v)
        = -fun x => ((φ k).normed volume ⋆[lsmul ℝ ℝ, volume] v) x - v x from by
          funext x; simp only [Pi.sub_apply, Pi.neg_apply]; ring, eLpNorm_neg]
    exact hkv

/-- **Meyers–Serrin (`H = W`), full multi-direction form.** If `u ∈ Lᵖ` has weak derivative
`v i` in each of finitely many directions `e i` (`1 ≤ p < ∞`), then a single smooth mollification
`w` simultaneously approximates `u` in `Lᵖ` and has weak derivatives `w' i` approximating each
`v i` in `Lᵖ`. Taking `e i = eᵢ` (the coordinate directions) gives density of `C^∞` in
`W^{1,p}(ℝⁿ)`. -/
theorem exists_contDiff_forall_isWeakDerivInDir {u : ℝⁿ → ℝ} {v : Fin n → ℝⁿ → ℝ}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hu : MemLp u p volume)
    (hv : ∀ i, MemLp (v i) p volume) (e : Fin n → ℝⁿ)
    (hweak : ∀ i, IsWeakDerivInDir univ (e i) u (v i)) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (w : ℝⁿ → ℝ) (w' : Fin n → ℝⁿ → ℝ), ContDiff ℝ ∞ w ∧ eLpNorm (u - w) p volume ≤ ε ∧
      ∀ i, IsWeakDerivInDir univ (e i) w (w' i) ∧ eLpNorm (v i - w' i) p volume ≤ ε := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hu_li : LocallyIntegrable u volume := hu.locallyIntegrable hp1
  have hv_li : ∀ i, LocallyIntegrable (v i) volume := fun i => (hv i).locallyIntegrable hp1
  set φ : ℕ → ContDiffBump (0 : ℝⁿ) := fun k =>
    ⟨1 / (k + 2 : ℝ), 1 / (k + 1 : ℝ), by positivity,
      one_div_lt_one_div_of_lt (by positivity) (by linarith)⟩ with hφdef
  have hφ : Tendsto (fun k => (φ k).rOut) atTop (𝓝 0) := by
    simpa [hφdef] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  -- all `n + 1` mollification errors are eventually `≤ ε`
  have hev : ∀ᶠ k in atTop,
      (eLpNorm (fun x => ((φ k).normed volume ⋆[lsmul ℝ ℝ, volume] u) x - u x) p volume ≤ ε) ∧
      ∀ i, eLpNorm (fun x =>
        ((φ k).normed volume ⋆[lsmul ℝ ℝ, volume] (v i)) x - (v i) x) p volume ≤ ε := by
    refine (ENNReal.tendsto_nhds_zero.mp (tendsto_eLpNorm_convolution_sub hp hu hφ) ε hε).and ?_
    exact eventually_all.mpr fun i =>
      ENNReal.tendsto_nhds_zero.mp (tendsto_eLpNorm_convolution_sub hp (hv i) hφ) ε hε
  obtain ⟨k, hku, hkv⟩ := hev.exists
  refine ⟨(φ k).normed volume ⋆[lsmul ℝ ℝ, volume] u,
          fun i => (φ k).normed volume ⋆[lsmul ℝ ℝ, volume] (v i), ?_, ?_, ?_⟩
  · exact (φ k).hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
      (φ k).contDiff_normed hu_li
  · rw [show u - ((φ k).normed volume ⋆[lsmul ℝ ℝ, volume] u)
        = -fun x => ((φ k).normed volume ⋆[lsmul ℝ ℝ, volume] u) x - u x from by
          funext x; simp only [Pi.sub_apply, Pi.neg_apply]; ring, eLpNorm_neg]
    exact hku
  · intro i
    refine ⟨isWeakDerivInDir_convolution (φ k).contDiff_normed (φ k).hasCompactSupport_normed
        hu_li (hv_li i) (e i) (hweak i), ?_⟩
    rw [show v i - ((φ k).normed volume ⋆[lsmul ℝ ℝ, volume] (v i))
        = -fun x => ((φ k).normed volume ⋆[lsmul ℝ ℝ, volume] (v i)) x - (v i) x from by
          funext x; simp only [Pi.sub_apply, Pi.neg_apply]; ring, eLpNorm_neg]
    exact hkv i

/-- **Compact-support mollification.**  A compactly supported `u ∈ W^{1,p}` (with weak derivatives
`v i`) is approximated in `W^{1,p}` by **smooth, compactly supported** functions: for every `ε > 0`
there is `w ∈ C^∞_c` with `‖u − w‖_p ≤ ε` and `‖v i − w'_i‖_p ≤ ε`.  Same construction as
Meyers–Serrin (`exists_contDiff_forall_isWeakDerivInDir`), additionally noting that the mollification
`η_δ ⋆ u` is compactly supported when `u` is (`HasCompactSupport.convolution`). -/
theorem exists_contDiff_hasCompactSupport_forall_isWeakDerivInDir_of_hasCompactSupport
    {u : ℝⁿ → ℝ} {v : Fin n → ℝⁿ → ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (hucs : HasCompactSupport u) (hu : MemLp u p volume) (hv : ∀ i, MemLp (v i) p volume)
    (e : Fin n → ℝⁿ) (hweak : ∀ i, IsWeakDerivInDir univ (e i) u (v i)) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (w : ℝⁿ → ℝ) (w' : Fin n → ℝⁿ → ℝ), ContDiff ℝ ∞ w ∧ HasCompactSupport w ∧
      eLpNorm (u - w) p volume ≤ ε ∧
      ∀ i, ContDiff ℝ ∞ (w' i) ∧ IsWeakDerivInDir univ (e i) w (w' i) ∧
        eLpNorm (v i - w' i) p volume ≤ ε := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hu_li : LocallyIntegrable u volume := hu.locallyIntegrable hp1
  have hv_li : ∀ i, LocallyIntegrable (v i) volume := fun i => (hv i).locallyIntegrable hp1
  set φ : ℕ → ContDiffBump (0 : ℝⁿ) := fun k =>
    ⟨1 / (k + 2 : ℝ), 1 / (k + 1 : ℝ), by positivity,
      one_div_lt_one_div_of_lt (by positivity) (by linarith)⟩ with hφdef
  have hφ : Tendsto (fun k => (φ k).rOut) atTop (𝓝 0) := by
    simpa [hφdef] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hev : ∀ᶠ k in atTop,
      (eLpNorm (fun x => ((φ k).normed volume ⋆[lsmul ℝ ℝ, volume] u) x - u x) p volume ≤ ε) ∧
      ∀ i, eLpNorm (fun x =>
        ((φ k).normed volume ⋆[lsmul ℝ ℝ, volume] (v i)) x - (v i) x) p volume ≤ ε := by
    refine (ENNReal.tendsto_nhds_zero.mp (tendsto_eLpNorm_convolution_sub hp hu hφ) ε hε).and ?_
    exact eventually_all.mpr fun i =>
      ENNReal.tendsto_nhds_zero.mp (tendsto_eLpNorm_convolution_sub hp (hv i) hφ) ε hε
  obtain ⟨k, hku, hkv⟩ := hev.exists
  refine ⟨(φ k).normed volume ⋆[lsmul ℝ ℝ, volume] u,
          fun i => (φ k).normed volume ⋆[lsmul ℝ ℝ, volume] (v i), ?_, ?_, ?_, ?_⟩
  · exact (φ k).hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
      (φ k).contDiff_normed hu_li
  · exact (φ k).hasCompactSupport_normed.convolution (lsmul ℝ ℝ) hucs
  · rw [show u - ((φ k).normed volume ⋆[lsmul ℝ ℝ, volume] u)
        = -fun x => ((φ k).normed volume ⋆[lsmul ℝ ℝ, volume] u) x - u x from by
          funext x; simp only [Pi.sub_apply, Pi.neg_apply]; ring, eLpNorm_neg]
    exact hku
  · intro i
    refine ⟨(φ k).hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
        (φ k).contDiff_normed (hv_li i),
      isWeakDerivInDir_convolution (φ k).contDiff_normed (φ k).hasCompactSupport_normed
        hu_li (hv_li i) (e i) (hweak i), ?_⟩
    rw [show v i - ((φ k).normed volume ⋆[lsmul ℝ ℝ, volume] (v i))
        = -fun x => ((φ k).normed volume ⋆[lsmul ℝ ℝ, volume] (v i)) x - (v i) x from by
          funext x; simp only [Pi.sub_apply, Pi.neg_apply]; ring, eLpNorm_neg]
    exact hkv i

/-! ### Sobolev embedding (Gagliardo–Nirenberg–Sobolev) -/

/-- **Gagliardo–Nirenberg–Sobolev embedding inequality** on `ℝⁿ`.  A continuously differentiable,
compactly supported `u` lies in `L^{p'}` with `‖u‖_{p'} ≲ ‖Du‖_p`, where `p'` is the Sobolev
conjugate `1/p' = 1/p − 1/n`.  A specialization of Mathlib's GNS inequality to the Euclidean
ambient space; with `isWeakDerivInDir_of_contDiff` the right-hand side is the `W^{1,p}` gradient
seminorm of `u`. -/
theorem exists_eLpNorm_le_eLpNorm_fderiv {u : ℝⁿ → ℝ} (hu : ContDiff ℝ 1 u)
    (h2u : HasCompactSupport u) {p p' : ℝ≥0} (hp : 1 ≤ p) (hn : 0 < n)
    (hp' : (p' : ℝ)⁻¹ = (p : ℝ)⁻¹ - (n : ℝ)⁻¹) :
    ∃ C : ℝ≥0, eLpNorm u p' volume ≤ C * eLpNorm (fderiv ℝ u) p volume :=
  ⟨_, eLpNorm_le_eLpNorm_fderiv_of_eq volume hu h2u hp
      (by rw [finrank_euclideanSpace_fin]; exact hn)
      (by rw [finrank_euclideanSpace_fin]; exact hp')⟩

/-- **Sobolev embedding into the full range** `L^q`, `1/p − 1/n ≤ 1/q` (so `q ≤ p*`).  For a
continuously differentiable `u` supported in a bounded set, `‖u‖_q ≲ ‖Du‖_p` (`1 ≤ p < n`). -/
theorem exists_eLpNorm_le_eLpNorm_fderiv_of_le {u : ℝⁿ → ℝ} {s : Set ℝⁿ} (hu : ContDiff ℝ 1 u)
    (h2u : u.support ⊆ s) {p q : ℝ≥0} (hp : 1 ≤ p) (hpn : p < n)
    (hpq : (p : ℝ)⁻¹ - (n : ℝ)⁻¹ ≤ (q : ℝ)⁻¹) (hs : Bornology.IsBounded s) :
    ∃ C : ℝ≥0, eLpNorm u q volume ≤ C * eLpNorm (fderiv ℝ u) p volume :=
  ⟨_, eLpNorm_le_eLpNorm_fderiv_of_le volume hu h2u hp
      (by rw [finrank_euclideanSpace_fin]; exact_mod_cast hpn)
      (by rw [finrank_euclideanSpace_fin]; exact hpq) hs⟩

/-! ### Poincaré's inequality -/

/-- **Poincaré's inequality** for `W₀^{1,p}` (Evans §5.6, Theorem 1, with `q = p`). For a
continuously differentiable `u` supported in a bounded set `s` and `1 ≤ p < n`, the `Lᵖ` norm of `u`
is controlled by the `Lᵖ` norm of its gradient: `‖u‖_p ≤ C ‖Du‖_p`. This is the case `q = p` of the
Sobolev–Poincaré estimate `exists_eLpNorm_le_eLpNorm_fderiv_of_le` (the full subcritical range
`1 ≤ q ≤ p*`); the subcritical condition `1/p − 1/n ≤ 1/q` holds trivially for `q = p`, since
`1/n ≥ 0`. -/
theorem exists_eLpNorm_self_le_eLpNorm_fderiv {u : ℝⁿ → ℝ} {s : Set ℝⁿ} (hu : ContDiff ℝ 1 u)
    (h2u : u.support ⊆ s) {p : ℝ≥0} (hp : 1 ≤ p) (hpn : p < n) (hs : Bornology.IsBounded s) :
    ∃ C : ℝ≥0, eLpNorm u p volume ≤ C * eLpNorm (fderiv ℝ u) p volume :=
  exists_eLpNorm_le_eLpNorm_fderiv_of_le hu h2u hp hpn
    (sub_le_self (p : ℝ)⁻¹ (by positivity)) hs

/-- **Scaled smooth cutoffs with controlled gradient.**  There is a uniform constant `M` such that
for every `R > 0` there is a smooth, compactly supported `χ : ℝⁿ → ℝ` equal to `1` on the ball of
radius `R`, with values in `[0,1]`, and gradient bounded by `M / R` everywhere.  Built by rescaling a
fixed `ContDiffBump` (radii `1 < 2`): `χ_R(x) = g(x/R)`, whose Fréchet derivative is
`(fderiv g)(x/R) ∘ (R⁻¹ • id)`, of norm `≤ (sup‖fderiv g‖)/R`.  This is the truncation device behind
density of `C^∞_c` in `W^{1,p}(ℝⁿ)`: the gradient term `(∇χ_R)·u` is `O(1/R)` in `Lᵖ`. -/
lemma exists_cutoff_family :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ R : ℝ, 0 < R → ∃ χ : ℝⁿ → ℝ,
      ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ (∀ x : ℝⁿ, ‖x‖ ≤ R → χ x = 1) ∧
      (∀ x, 0 ≤ χ x) ∧ (∀ x, χ x ≤ 1) ∧ (∀ x, ‖fderiv ℝ χ x‖ ≤ M / R) := by
  set g : ContDiffBump (0 : ℝⁿ) := ⟨1, 2, one_pos, one_lt_two⟩ with hgdef
  have hrIn : g.rIn = 1 := rfl
  have hrOut : g.rOut = 2 := rfl
  obtain ⟨M, hM⟩ := (g.hasCompactSupport.fderiv (𝕜 := ℝ)).exists_bound_of_continuous
    ((g.contDiff : ContDiff ℝ 2 _).continuous_fderiv (by norm_num))
  refine ⟨M, le_trans (norm_nonneg _) (hM 0), fun R hR => ?_⟩
  refine ⟨fun x => g (R⁻¹ • x), g.contDiff.comp (contDiff_const_smul _), ?_, ?_,
    fun x => g.nonneg, fun x => g.le_one, ?_⟩
  · -- compact support, inside `closedBall 0 (2R)`
    apply HasCompactSupport.intro (isCompact_closedBall (0 : ℝⁿ) (2 * R))
    intro x hx
    rw [mem_closedBall_zero_iff, not_le] at hx
    refine Function.notMem_support.mp ?_
    rw [g.support_eq, hrOut, mem_ball_zero_iff, not_lt, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hR)]
    calc (2 : ℝ) = R⁻¹ * (2 * R) := by field_simp
      _ ≤ R⁻¹ * ‖x‖ := by
          exact mul_le_mul_of_nonneg_left hx.le (le_of_lt (inv_pos.mpr hR))
  · -- equals `1` on `closedBall 0 R`
    intro x hx
    refine g.one_of_mem_closedBall ?_
    rw [mem_closedBall_zero_iff, hrIn, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
    calc R⁻¹ * ‖x‖ ≤ R⁻¹ * R := mul_le_mul_of_nonneg_left hx (le_of_lt (inv_pos.mpr hR))
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hR)
  · -- gradient bound `‖∇χ_R‖ ≤ M / R`
    intro x
    set L : ℝⁿ →L[ℝ] ℝⁿ := (R⁻¹ : ℝ) • ContinuousLinearMap.id ℝ ℝⁿ with hLdef
    have hLx : ∀ y : ℝⁿ, L y = R⁻¹ • y := fun y => by simp [hLdef]
    have hLfd : fderiv ℝ (fun y : ℝⁿ => g (R⁻¹ • y)) x = (fderiv ℝ g (R⁻¹ • x)).comp L := by
      have hcomp : (fun y : ℝⁿ => g (R⁻¹ • y)) = ⇑g ∘ ⇑L := by
        funext y; rw [Function.comp_apply, hLx]
      rw [hcomp, fderiv_comp x
        ((g.contDiff : ContDiff ℝ 2 _).differentiable (by norm_num)).differentiableAt
        L.differentiableAt, L.hasFDerivAt.fderiv, hLx]
    rw [hLfd]
    calc ‖(fderiv ℝ g (R⁻¹ • x)).comp L‖
        ≤ ‖fderiv ℝ g (R⁻¹ • x)‖ * ‖L‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ M * R⁻¹ := by
          refine mul_le_mul (hM _) ?_ (norm_nonneg _) (le_trans (norm_nonneg _) (hM 0))
          rw [hLdef, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
          calc R⁻¹ * ‖ContinuousLinearMap.id ℝ ℝⁿ‖ ≤ R⁻¹ * 1 :=
                mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (le_of_lt (inv_pos.mpr hR))
            _ = R⁻¹ := mul_one _
      _ = M / R := (div_eq_mul_inv M R).symm

/-- **The truncation gradient term vanishes in `Lᵖ`.**  If the cutoffs `χ_k` have gradient
`‖∇χ_k‖ ≤ M/(k+1)` (as produced by `exists_cutoff_family`), then for `u ∈ Lᵖ` the term
`(∂_e χ_k)·u` tends to `0` in `Lᵖ`: pointwise `‖(∂_e χ_k x)·u x‖ ≤ (M/(k+1)·‖e‖)·‖u x‖`, so the
`Lᵖ` norm is `≤ ofReal(M/(k+1)·‖e‖)·‖u‖_p → 0`. -/
lemma tendsto_eLpNorm_fderiv_cutoff_mul {u : ℝⁿ → ℝ} {p : ℝ≥0∞} (hu : MemLp u p volume)
    {χ : ℕ → ℝⁿ → ℝ} {M : ℝ} (hM : 0 ≤ M) (e : ℝⁿ)
    (hbd : ∀ k x, ‖fderiv ℝ (χ k) x‖ ≤ M / (k + 1)) :
    Tendsto (fun k => eLpNorm (fun x => fderiv ℝ (χ k) x e * u x) p volume) atTop (𝓝 0) := by
  have hcoef : ∀ k : ℕ, (0 : ℝ) ≤ M / (k + 1) * ‖e‖ :=
    fun k => mul_nonneg (div_nonneg hM (by positivity)) (norm_nonneg e)
  have hb : ∀ k, eLpNorm (fun x => fderiv ℝ (χ k) x e * u x) p volume
      ≤ ENNReal.ofReal (M / (k + 1) * ‖e‖) * eLpNorm u p volume := by
    intro k
    have hmono : eLpNorm (fun x => fderiv ℝ (χ k) x e * u x) p volume
        ≤ eLpNorm ((M / (k + 1) * ‖e‖ : ℝ) • u) p volume := by
      refine eLpNorm_mono_ae (Eventually.of_forall fun x => ?_)
      rw [norm_mul, Pi.smul_apply, smul_eq_mul, norm_mul, Real.norm_eq_abs (M / (k + 1) * ‖e‖),
        abs_of_nonneg (hcoef k)]
      gcongr
      calc ‖fderiv ℝ (χ k) x e‖ ≤ ‖fderiv ℝ (χ k) x‖ * ‖e‖ := (fderiv ℝ (χ k) x).le_opNorm e
        _ ≤ M / (k + 1) * ‖e‖ := by gcongr; exact hbd k x
    rwa [eLpNorm_const_smul, Real.enorm_eq_ofReal (hcoef k)] at hmono
  have hrhs : Tendsto (fun k : ℕ => ENNReal.ofReal (M / (k + 1) * ‖e‖) * eLpNorm u p volume)
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => M / (k + 1)) atTop (𝓝 0) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul M
    have hreal : Tendsto (fun k : ℕ => M / (k + 1) * ‖e‖) atTop (𝓝 0) := by
      simpa using h1.mul_const ‖e‖
    have h2 : Tendsto (fun k : ℕ => ENNReal.ofReal (M / (k + 1) * ‖e‖)) atTop (𝓝 0) := by
      rw [show (0 : ℝ≥0∞) = ENNReal.ofReal 0 from ENNReal.ofReal_zero.symm]
      exact (ENNReal.continuous_ofReal.tendsto 0).comp hreal
    simpa using ENNReal.Tendsto.mul_const h2 (Or.inr hu.eLpNorm_ne_top)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hrhs
    (fun k => zero_le _) hb

/-- **The truncation `χ_k·u → u` in `Lᵖ`.**  If the cutoffs `χ_k` equal `1` on `B(0,k+1)` and take
values in `[0,1]`, then `χ_k·u → u` in `Lᵖ` for `u ∈ Lᵖ` (`1 ≤ p < ∞`).  Dominated convergence:
`‖χ_k u − u‖ ≤ ‖u‖` pointwise (since `|χ_k − 1| ≤ 1`) and `→ 0` (each `x` is eventually inside the
ball where `χ_k = 1`), with dominating function `‖u‖ₑ^p ∈ L¹`. -/
lemma tendsto_eLpNorm_cutoff_mul_sub {u : ℝⁿ → ℝ} {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ⊤)
    (hu : MemLp u p volume) {χ : ℕ → ℝⁿ → ℝ}
    (hχ1 : ∀ (k : ℕ) (x : ℝⁿ), ‖x‖ ≤ (k : ℝ) + 1 → χ k x = 1) (hχ01 : ∀ k x, 0 ≤ χ k x ∧ χ k x ≤ 1)
    (hχmeas : ∀ k, AEStronglyMeasurable (χ k) volume) :
    Tendsto (fun k => eLpNorm (fun x => χ k x * u x - u x) p volume) atTop (𝓝 0) := by
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  -- pointwise domination `‖χ_k u − u‖ₑ ≤ ‖u‖ₑ`
  have hgle : ∀ k (x : ℝⁿ), ‖χ k x * u x - u x‖ₑ ≤ ‖u x‖ₑ := by
    intro k x
    rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [show χ k x * u x - u x = (χ k x - 1) * u x from by ring, abs_mul]
    calc |χ k x - 1| * |u x| ≤ 1 * |u x| := by
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          rw [abs_le]; exact ⟨by linarith [(hχ01 k x).1], by linarith [(hχ01 k x).2]⟩
      _ = |u x| := one_mul _
  -- the four ingredients of dominated convergence (in `ℝ≥0∞`)
  have hF_meas : ∀ k, AEMeasurable (fun x => ‖χ k x * u x - u x‖ₑ ^ p.toReal) volume := fun k =>
    (((hχmeas k).mul hu.aestronglyMeasurable).sub hu.aestronglyMeasurable).enorm.pow_const _
  have hbound : ∀ k, (fun x => ‖χ k x * u x - u x‖ₑ ^ p.toReal)
      ≤ᵐ[volume] fun x => ‖u x‖ₑ ^ p.toReal :=
    fun k => Eventually.of_forall fun x => ENNReal.rpow_le_rpow (hgle k x) hpr.le
  have hfin : ∫⁻ x, ‖u x‖ₑ ^ p.toReal ∂volume ≠ (⊤ : ℝ≥0∞) :=
    (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 hp hu.eLpNorm_lt_top).ne
  have hlim : ∀ x : ℝⁿ, Tendsto (fun k => ‖χ k x * u x - u x‖ₑ ^ p.toReal) atTop (𝓝 0) := by
    intro x
    obtain ⟨N, hN⟩ := exists_nat_ge ‖x‖
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop N] with k hk
    have hxk : ‖x‖ ≤ (k : ℝ) + 1 := by
      have : (N : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      linarith
    rw [hχ1 k x hxk]
    simp only [one_mul, sub_self, enorm_zero, ENNReal.zero_rpow_of_pos hpr]
  -- reduce `eLpNorm` to the lintegral and pass to the limit
  rw [show (fun k => eLpNorm (fun x => χ k x * u x - u x) p volume)
      = fun k => (∫⁻ x, ‖χ k x * u x - u x‖ₑ ^ p.toReal ∂volume) ^ (1 / p.toReal) from
    funext fun k => eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp]
  have hlint : Tendsto (fun k => ∫⁻ x, ‖χ k x * u x - u x‖ₑ ^ p.toReal ∂volume) atTop (𝓝 0) := by
    simpa using tendsto_lintegral_of_dominated_convergence'
      (fun x => ‖u x‖ₑ ^ p.toReal) hF_meas hbound hfin (Eventually.of_forall hlim)
  have hres := hlint.ennrpow_const (1 / p.toReal)
  rwa [ENNReal.zero_rpow_of_pos (by positivity)] at hres

/-- **Truncation: compactly supported functions are dense in `W^{1,p}`.**  Given `u ∈ W^{1,p}(ℝⁿ)`
(with weak derivatives `v i`), for every `ε > 0` there is a **compactly supported** `w ∈ W^{1,p}`
with `‖u − w‖_p ≤ ε` and `‖v i − w'_i‖_p ≤ ε` for each direction, where `w'_i` is the weak
derivative of `w`.  Take `w = χ_k·u` for a large cutoff `χ_k`: its weak derivative is
`χ_k·v_i + (∂_{e_i}χ_k)·u` (the weak Leibniz rule `IsWeakDerivInDir.mul_smooth`), and both error
families vanish in `Lᵖ` by `tendsto_eLpNorm_cutoff_mul_sub` (applied to `u` and each `v i`) and
`tendsto_eLpNorm_fderiv_cutoff_mul`.  A single `k` works for all `n` directions
(`Filter.eventually_all`). -/
theorem exists_hasCompactSupport_forall_isWeakDerivInDir {u : ℝⁿ → ℝ} {v : Fin n → ℝⁿ → ℝ}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hu : MemLp u p volume)
    (hv : ∀ i, MemLp (v i) p volume) (e : Fin n → ℝⁿ)
    (hweak : ∀ i, IsWeakDerivInDir univ (e i) u (v i)) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (w : ℝⁿ → ℝ) (w' : Fin n → ℝⁿ → ℝ), HasCompactSupport w ∧ MemLp w p volume ∧
      (∀ i, MemLp (w' i) p volume) ∧ eLpNorm (u - w) p volume ≤ ε ∧
      ∀ i, IsWeakDerivInDir univ (e i) w (w' i) ∧ eLpNorm (v i - w' i) p volume ≤ ε := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hp0 : p ≠ 0 := (lt_of_lt_of_le one_pos hp1).ne'
  obtain ⟨M, hM, hχfam⟩ := exists_cutoff_family (n := n)
  choose χ hχcd hχcs hχ1 hχ0 hχ1' hχbd using fun k : ℕ => hχfam ((k : ℝ) + 1) (by positivity)
  have hχmeas : ∀ k, AEStronglyMeasurable (χ k) volume :=
    fun k => (hχcd k).continuous.aestronglyMeasurable
  have hχ01 : ∀ k x, 0 ≤ χ k x ∧ χ k x ≤ 1 := fun k x => ⟨hχ0 k x, hχ1' k x⟩
  have hχabs : ∀ k x, |χ k x| ≤ 1 := fun k x => abs_le.mpr ⟨by linarith [(hχ01 k x).1], (hχ01 k x).2⟩
  -- a single `k` making all `2n+1` errors small
  have hε2 : (0 : ℝ≥0∞) < ε / 2 := ENNReal.half_pos hε.ne'
  have evU : ∀ᶠ k in atTop, eLpNorm (fun x => χ k x * u x - u x) p volume ≤ ε :=
    ENNReal.tendsto_nhds_zero.mp (tendsto_eLpNorm_cutoff_mul_sub hp0 hp hu hχ1 hχ01 hχmeas) ε hε
  have evV : ∀ᶠ k in atTop, ∀ i, eLpNorm (fun x => χ k x * v i x - v i x) p volume ≤ ε / 2 :=
    eventually_all.mpr fun i =>
      ENNReal.tendsto_nhds_zero.mp (tendsto_eLpNorm_cutoff_mul_sub hp0 hp (hv i) hχ1 hχ01 hχmeas)
        (ε / 2) hε2
  have evG : ∀ᶠ k in atTop, ∀ i,
      eLpNorm (fun x => fderiv ℝ (χ k) x (e i) * u x) p volume ≤ ε / 2 :=
    eventually_all.mpr fun i =>
      ENNReal.tendsto_nhds_zero.mp (tendsto_eLpNorm_fderiv_cutoff_mul hu hM (e i) hχbd) (ε / 2) hε2
  obtain ⟨k, hkU, hkV, hkG⟩ := (evU.and (evV.and evG)).exists
  -- `∂_{e_i} χ_k` is continuous
  have hdχc : ∀ i, Continuous (fun x => fderiv ℝ (χ k) x (e i)) := fun i =>
    ((hχcd k).continuous_fderiv (by norm_num)).clm_apply continuous_const
  -- membership facts via domination
  have hmemχ : ∀ {g : ℝⁿ → ℝ}, MemLp g p volume → MemLp (fun x => χ k x * g x) p volume :=
    fun {g} hg => hg.mono ((hχmeas k).mul hg.aestronglyMeasurable) <| Eventually.of_forall fun x => by
      rw [norm_mul]
      calc ‖χ k x‖ * ‖g x‖ ≤ 1 * ‖g x‖ := by gcongr; rw [Real.norm_eq_abs]; exact hχabs k x
        _ = ‖g x‖ := one_mul _
  have hCnn : ∀ i, (0 : ℝ) ≤ M / (k + 1) * ‖e i‖ :=
    fun i => mul_nonneg (div_nonneg hM (by positivity)) (norm_nonneg _)
  have hmemdχu : ∀ i, MemLp (fun x => fderiv ℝ (χ k) x (e i) * u x) p volume := fun i =>
    (hu.const_smul (M / (k + 1) * ‖e i‖)).mono
      ((hdχc i).aestronglyMeasurable.mul hu.aestronglyMeasurable) <| Eventually.of_forall fun x => by
        rw [norm_mul, Pi.smul_apply, norm_smul, Real.norm_eq_abs (M / (k + 1) * ‖e i‖),
          abs_of_nonneg (hCnn i)]
        gcongr
        calc ‖fderiv ℝ (χ k) x (e i)‖ ≤ ‖fderiv ℝ (χ k) x‖ * ‖e i‖ := (fderiv ℝ (χ k) x).le_opNorm _
          _ ≤ M / (k + 1) * ‖e i‖ := by gcongr; exact hχbd k x
  refine ⟨fun x => χ k x * u x, fun i x => χ k x * v i x + fderiv ℝ (χ k) x (e i) * u x,
    (hχcs k).mul_right, hmemχ hu, fun i => (hmemχ (hv i)).add (hmemdχu i), ?_, fun i => ⟨?_, ?_⟩⟩
  · rw [eLpNorm_sub_comm]; exact hkU
  · exact (hweak i).mul_smooth (hu.locallyIntegrable hp1) ((hv i).locallyIntegrable hp1) (hχcd k)
  · have hAm : AEStronglyMeasurable (fun x => χ k x * v i x - v i x) volume :=
      ((hχmeas k).mul (hv i).aestronglyMeasurable).sub (hv i).aestronglyMeasurable
    have hBm : AEStronglyMeasurable (fun x => fderiv ℝ (χ k) x (e i) * u x) volume :=
      (hdχc i).aestronglyMeasurable.mul hu.aestronglyMeasurable
    rw [show (v i - fun x => χ k x * v i x + fderiv ℝ (χ k) x (e i) * u x)
        = -((fun x => χ k x * v i x - v i x) + fun x => fderiv ℝ (χ k) x (e i) * u x) from by
          funext x; simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply]; ring, eLpNorm_neg]
    calc eLpNorm ((fun x => χ k x * v i x - v i x)
            + fun x => fderiv ℝ (χ k) x (e i) * u x) p volume
        ≤ eLpNorm (fun x => χ k x * v i x - v i x) p volume
            + eLpNorm (fun x => fderiv ℝ (χ k) x (e i) * u x) p volume := eLpNorm_add_le hAm hBm hp1
      _ ≤ ε / 2 + ε / 2 := add_le_add (hkV i) (hkG i)
      _ = ε := ENNReal.add_halves ε

/-- **Sobolev embedding for all of `W^{1,p}` (passing to the limit).**  The
Gagliardo–Nirenberg–Sobolev inequality, proved above for `C¹` compactly supported functions,
extends to any `u` that is the `W^{1,p}`-limit of such functions: if a sequence `uk` of `C¹`
compactly supported functions converges to `u` in `Lᵖ` and its gradients converge to `V` in `Lᵖ`,
then `u ∈ L^{p*}` with the same constant,
`‖u‖_{p*} ≤ C‖V‖_p`.

This is the analyst's standard density argument made precise: the GNS constant
`SNormLESNormFDerivOfEqConst` is **uniform** across the sequence; `Lᵖ`-convergence gives an a.e.
convergent subsequence (`tendstoInMeasure_of_tendsto_eLpNorm` then
`TendstoInMeasure.exists_seq_tendsto_ae`); and Fatou lower-semicontinuity of the seminorm
(`eLpNorm'_lim_le_liminf_eLpNorm'`) passes the inequality to the limit, the right-hand side
converging because `‖fderiv uk‖_p → ‖V‖_p` (norm-continuity in `Lᵖ`).  Combined with the
Meyers–Serrin density above, this delivers the embedding on the whole space `W^{1,p}(ℝⁿ)`. -/
theorem exists_eLpNorm_le_eLpNorm_fderiv_of_tendsto {u : ℝⁿ → ℝ} {V : ℝⁿ → (ℝⁿ →L[ℝ] ℝ)}
    {p p' : ℝ≥0} (hp : 1 ≤ p) (hn : 0 < n) (hpn : p < n)
    (hp' : (p' : ℝ)⁻¹ = (p : ℝ)⁻¹ - (n : ℝ)⁻¹)
    (hu_meas : AEStronglyMeasurable u volume) (hV : MemLp V (p : ℝ≥0∞) volume)
    {uk : ℕ → ℝⁿ → ℝ} (hC1 : ∀ k, ContDiff ℝ 1 (uk k)) (hcs : ∀ k, HasCompactSupport (uk k))
    (hUconv : Tendsto (fun k => eLpNorm (uk k - u) (p : ℝ≥0∞) volume) atTop (𝓝 0))
    (hVconv : Tendsto (fun k => eLpNorm (fderiv ℝ (uk k) - V) (p : ℝ≥0∞) volume) atTop (𝓝 0)) :
    ∃ C : ℝ≥0, eLpNorm u (p' : ℝ≥0∞) volume ≤ C * eLpNorm V (p : ℝ≥0∞) volume := by
  haveI : Fact (1 ≤ (p : ℝ≥0∞)) := ⟨by exact_mod_cast hp⟩
  -- positivity / finiteness bookkeeping for the exponents
  have hp_pos' : (0 : ℝ≥0) < p := lt_of_lt_of_le zero_lt_one hp
  have hp0 : (p : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr hp_pos'.ne'
  have hp_posR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp_pos'
  have hpnR : (p : ℝ) < (n : ℝ) := by exact_mod_cast hpn
  have h2 : (0 : ℝ) < (p' : ℝ)⁻¹ := by
    rw [hp', sub_pos, inv_eq_one_div, inv_eq_one_div]
    exact one_div_lt_one_div_of_lt hp_posR hpnR
  have hpr_pos : (0 : ℝ) < (p' : ℝ) := inv_pos.mp h2
  have hp'pos : (0 : ℝ≥0) < p' := by exact_mod_cast hpr_pos
  have hp'0 : (p' : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr hp'pos.ne'
  have hp'top : (p' : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hpr : ((p' : ℝ≥0∞)).toReal = (p' : ℝ) := by simp
  -- `eLpNorm` ↔ `eLpNorm'` (real exponent) at the conjugate exponent `p'`
  have hconv_u : eLpNorm u (p' : ℝ≥0∞) volume = eLpNorm' u (p' : ℝ) volume := by
    rw [eLpNorm_eq_eLpNorm' hp'0 hp'top, hpr]
  have hee : ∀ f : ℝⁿ → ℝ, eLpNorm' f (p' : ℝ) volume = eLpNorm f (p' : ℝ≥0∞) volume := by
    intro f; rw [eLpNorm_eq_eLpNorm' hp'0 hp'top, hpr]
  -- the **uniform** GNS constant (same for every member of the sequence)
  obtain ⟨C, hGNS⟩ : ∃ C : ℝ≥0, ∀ k, eLpNorm (uk k) (p' : ℝ≥0∞) volume
      ≤ (C : ℝ≥0∞) * eLpNorm (fderiv ℝ (uk k)) (p : ℝ≥0∞) volume :=
    ⟨_, fun k => eLpNorm_le_eLpNorm_fderiv_of_eq volume (hC1 k) (hcs k) hp
      (by rw [finrank_euclideanSpace_fin]; exact hn)
      (by rw [finrank_euclideanSpace_fin]; exact hp')⟩
  -- gradients of the (`C¹`, compactly supported) members are `Lᵖ`
  have hgrad_mem : ∀ k, MemLp (fderiv ℝ (uk k)) (p : ℝ≥0∞) volume := fun k =>
    ((hC1 k).continuous_fderiv one_ne_zero).memLp_of_hasCompactSupport ((hcs k).fderiv (𝕜 := ℝ))
  have hmeas_uk : ∀ k, AEStronglyMeasurable (uk k) volume :=
    fun k => (hC1 k).continuous.aestronglyMeasurable
  -- an a.e. convergent subsequence from `Lᵖ`-convergence
  have htim : TendstoInMeasure volume uk atTop u :=
    tendstoInMeasure_of_tendsto_eLpNorm hp0 hmeas_uk hu_meas hUconv
  obtain ⟨ns, hns_mono, hns_ae⟩ := htim.exists_seq_tendsto_ae
  -- Fatou lower-semicontinuity of the seminorm along the subsequence
  have hfatou : eLpNorm' u (p' : ℝ) volume
      ≤ atTop.liminf (fun k => eLpNorm' (uk (ns k)) (p' : ℝ) volume) :=
    Lp.eLpNorm'_lim_le_liminf_eLpNorm' hpr_pos (fun k => hmeas_uk (ns k)) hns_ae
  have hbound_k : ∀ k, eLpNorm' (uk (ns k)) (p' : ℝ) volume
      ≤ (C : ℝ≥0∞) * eLpNorm (fderiv ℝ (uk (ns k))) (p : ℝ≥0∞) volume := by
    intro k; rw [hee]; exact hGNS (ns k)
  -- the right-hand side converges: `‖fderiv uk‖_p → ‖V‖_p` by norm-continuity in `Lᵖ`
  have hGtend : Tendsto (fun k => (hgrad_mem k).toLp (fderiv ℝ (uk k))) atTop (𝓝 (hV.toLp V)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have hd : (fun k => dist ((hgrad_mem k).toLp (fderiv ℝ (uk k))) (hV.toLp V))
        = (fun k => (eLpNorm (fderiv ℝ (uk k) - V) (p : ℝ≥0∞) volume).toReal) := by
      funext k
      rw [Lp.dist_def]
      congr 1
      refine eLpNorm_congr_ae ?_
      filter_upwards [MemLp.coeFn_toLp (hgrad_mem k), MemLp.coeFn_toLp hV] with x hx hxv
      simp only [Pi.sub_apply, hx, hxv]
    rw [hd]
    simpa using (ENNReal.continuousAt_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).tendsto.comp hVconv
  have hnf : ∀ k, ‖(hgrad_mem k).toLp (fderiv ℝ (uk k))‖
      = (eLpNorm (fderiv ℝ (uk k)) (p : ℝ≥0∞) volume).toReal := fun k => by
    rw [Lp.norm_def]; congr 1; exact eLpNorm_congr_ae (MemLp.coeFn_toLp (hgrad_mem k))
  have hnV : ‖hV.toLp V‖ = (eLpNorm V (p : ℝ≥0∞) volume).toReal := by
    rw [Lp.norm_def]; congr 1; exact eLpNorm_congr_ae (MemLp.coeFn_toLp hV)
  have hgradnorm : Tendsto (fun k => eLpNorm (fderiv ℝ (uk k)) (p : ℝ≥0∞) volume) atTop
      (𝓝 (eLpNorm V (p : ℝ≥0∞) volume)) := by
    rw [← ENNReal.tendsto_toReal_iff (fun k => (hgrad_mem k).eLpNorm_ne_top) hV.eLpNorm_ne_top]
    have hnorm := hGtend.norm
    rw [hnV] at hnorm
    simpa only [hnf] using hnorm
  have hmul_tendsto : Tendsto (fun k => (C : ℝ≥0∞)
        * eLpNorm (fderiv ℝ (uk (ns k))) (p : ℝ≥0∞) volume) atTop
      (𝓝 ((C : ℝ≥0∞) * eLpNorm V (p : ℝ≥0∞) volume)) :=
    ENNReal.Tendsto.const_mul (hgradnorm.comp hns_mono.tendsto_atTop) (Or.inr ENNReal.coe_ne_top)
  have hgrad_liminf : atTop.liminf (fun k => (C : ℝ≥0∞)
        * eLpNorm (fderiv ℝ (uk (ns k))) (p : ℝ≥0∞) volume)
      = (C : ℝ≥0∞) * eLpNorm V (p : ℝ≥0∞) volume := hmul_tendsto.liminf_eq
  -- assemble
  refine ⟨C, ?_⟩
  rw [hconv_u]
  exact hfatou.trans ((Filter.liminf_le_liminf (Eventually.of_forall hbound_k)).trans
    (le_of_eq hgrad_liminf))

/-- **`C^∞_c` is dense in `W^{1,p}(ℝⁿ)`.**  For `u ∈ W^{1,p}` (weak derivatives `v i`) and `ε > 0`
there is a **smooth, compactly supported** `w` with `‖u − w‖_p ≤ ε` and `‖v i − w'_i‖_p ≤ ε` for
each direction (`w'_i` the weak derivative of `w`).  This combines truncation
(`exists_hasCompactSupport_forall_isWeakDerivInDir`, ε/2) with compact-support mollification
(`…_of_hasCompactSupport`, ε/2) and the triangle inequality — removing the approximation hypothesis
from the Sobolev embedding (the resulting sequence feeds
`exists_eLpNorm_le_eLpNorm_fderiv_of_tendsto`). -/
theorem exists_contDiff_hasCompactSupport_forall_isWeakDerivInDir {u : ℝⁿ → ℝ}
    {v : Fin n → ℝⁿ → ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hu : MemLp u p volume)
    (hv : ∀ i, MemLp (v i) p volume) (e : Fin n → ℝⁿ)
    (hweak : ∀ i, IsWeakDerivInDir univ (e i) u (v i)) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (w : ℝⁿ → ℝ) (w' : Fin n → ℝⁿ → ℝ), ContDiff ℝ ∞ w ∧ HasCompactSupport w ∧
      eLpNorm (u - w) p volume ≤ ε ∧
      ∀ i, ContDiff ℝ ∞ (w' i) ∧ IsWeakDerivInDir univ (e i) w (w' i) ∧
        eLpNorm (v i - w' i) p volume ≤ ε := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  obtain ⟨w₀, w₀', hw₀cs, hw₀mem, hw₀'mem, hw₀u, hw₀i⟩ :=
    exists_hasCompactSupport_forall_isWeakDerivInDir hp hu hv e hweak (ENNReal.half_pos hε.ne')
  obtain ⟨w, w', hwcd, hwcs, hww₀, hwi⟩ :=
    exists_contDiff_hasCompactSupport_forall_isWeakDerivInDir_of_hasCompactSupport hp hw₀cs hw₀mem
      hw₀'mem e (fun i => (hw₀i i).1) (ENNReal.half_pos hε.ne')
  refine ⟨w, w', hwcd, hwcs, ?_, fun i => ⟨(hwi i).1, (hwi i).2.1, ?_⟩⟩
  · have he : u - w = (u - w₀) + (w₀ - w) := by
      funext x; simp only [Pi.sub_apply, Pi.add_apply]; ring
    rw [he]
    calc eLpNorm ((u - w₀) + (w₀ - w)) p volume
        ≤ eLpNorm (u - w₀) p volume + eLpNorm (w₀ - w) p volume :=
          eLpNorm_add_le (hu.aestronglyMeasurable.sub hw₀mem.aestronglyMeasurable)
            (hw₀mem.aestronglyMeasurable.sub hwcd.continuous.aestronglyMeasurable) hp1
      _ ≤ ε / 2 + ε / 2 := add_le_add hw₀u hww₀
      _ = ε := ENNReal.add_halves ε
  · have he : v i - w' i = (v i - w₀' i) + (w₀' i - w' i) := by
      funext x; simp only [Pi.sub_apply, Pi.add_apply]; ring
    rw [he]
    calc eLpNorm ((v i - w₀' i) + (w₀' i - w' i)) p volume
        ≤ eLpNorm (v i - w₀' i) p volume + eLpNorm (w₀' i - w' i) p volume :=
          eLpNorm_add_le ((hv i).aestronglyMeasurable.sub (hw₀'mem i).aestronglyMeasurable)
            ((hw₀'mem i).aestronglyMeasurable.sub (hwi i).1.continuous.aestronglyMeasurable) hp1
      _ ≤ ε / 2 + ε / 2 := add_le_add (hw₀i i).2 (hwi i).2.2
      _ = ε := ENNReal.add_halves ε

/-- **Operator norm of a functional on `ℝⁿ` is bounded by the sum of its coordinate components.**
For `L : ℝⁿ →L[ℝ] ℝ`, `‖L‖ ≤ ∑ᵢ ‖L eᵢ‖` (`eᵢ` the standard basis), via Riesz representation
`L = ⟪g, ·⟫` with `g = (toDual).symm L`, `‖L‖ = ‖g‖`, the `ℓ²≤ℓ¹` bound, and `g i = L eᵢ`.  This is
the bridge from per-direction control of a derivative to control of the full Fréchet derivative as a
single continuous-linear map, turning per-coordinate `Lᵖ`-convergence into `Lᵖ`-convergence of
`fderiv`. -/
lemma opNorm_le_sum_apply_single (L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :
    ‖L‖ ≤ ∑ i, ‖L (EuclideanSpace.single i (1 : ℝ))‖ := by
  set g : EuclideanSpace ℝ (Fin n) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm L with hg
  have hgi : ∀ i, L (EuclideanSpace.single i (1 : ℝ)) = g i := by
    intro i
    have hL : L = InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n)) g := by
      rw [hg, LinearIsometryEquiv.apply_symm_apply]
    rw [hL, InnerProductSpace.toDual_apply_apply]
    exact (EuclideanSpace.inner_single_right i (1 : ℝ) g).trans (by simp)
  have hnorm : ‖L‖ = ‖g‖ := by rw [hg]; exact (LinearIsometryEquiv.norm_map _ L).symm
  rw [hnorm, EuclideanSpace.norm_eq]
  have hsq : ∑ i, ‖g i‖ ^ 2 ≤ (∑ i, ‖g i‖) ^ 2 := by
    rw [sq, Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [sq]
    exact mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (fun j _ => norm_nonneg _) (Finset.mem_univ i)) (norm_nonneg _)
  calc Real.sqrt (∑ i, ‖g i‖ ^ 2) ≤ Real.sqrt ((∑ i, ‖g i‖) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ∑ i, ‖g i‖ := Real.sqrt_sq (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    _ = ∑ i, ‖L (EuclideanSpace.single i (1 : ℝ))‖ := by simp_rw [hgi]

/-- **`Lᵖ` control of a derivative `ℝⁿ →L ℝ` by its coordinate components.**  For CLM-valued
`F, G`, `‖F − G‖_p ≤ ∑ᵢ ‖(F − G)·eᵢ‖_p`.  Pointwise `opNorm_le_sum_apply_single` plus the
`Lᵖ` triangle inequality (`eLpNorm_sum_le`).  Turns per-direction `Lᵖ`-convergence of weak partials
into `Lᵖ`-convergence of the full Fréchet derivative. -/
lemma eLpNorm_clm_sub_le_sum
    {F G : EuclideanSpace ℝ (Fin n) → (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)}
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hF : AEStronglyMeasurable F volume) (hG : AEStronglyMeasurable G volume) :
    eLpNorm (F - G) p volume ≤ ∑ i, eLpNorm
      (fun x => F x (EuclideanSpace.single i (1 : ℝ)) - G x (EuclideanSpace.single i (1 : ℝ)))
      p volume := by
  have hD : ∀ i, AEStronglyMeasurable
      (fun x => F x (EuclideanSpace.single i (1 : ℝ)) - G x (EuclideanSpace.single i (1 : ℝ)))
      volume := fun i =>
    (((ContinuousLinearMap.apply ℝ ℝ
          (EuclideanSpace.single i (1 : ℝ))).continuous.comp_aestronglyMeasurable hF).sub
      ((ContinuousLinearMap.apply ℝ ℝ
          (EuclideanSpace.single i (1 : ℝ))).continuous.comp_aestronglyMeasurable hG))
  have hpt : ∀ x, ‖(F - G) x‖ ≤
      ∑ i, ‖F x (EuclideanSpace.single i (1 : ℝ)) - G x (EuclideanSpace.single i (1 : ℝ))‖ := by
    intro x
    rw [Pi.sub_apply]
    refine le_trans (opNorm_le_sum_apply_single (F x - G x)) (le_of_eq ?_)
    exact Finset.sum_congr rfl fun i _ => by rw [ContinuousLinearMap.sub_apply]
  calc eLpNorm (F - G) p volume
      ≤ eLpNorm (∑ i, fun x => ‖F x (EuclideanSpace.single i (1 : ℝ))
            - G x (EuclideanSpace.single i (1 : ℝ))‖) p volume := by
        refine eLpNorm_mono_ae (Eventually.of_forall fun x => ?_)
        rw [Finset.sum_apply, Real.norm_eq_abs,
          abs_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)]
        exact hpt x
    _ ≤ ∑ i, eLpNorm (fun x => ‖F x (EuclideanSpace.single i (1 : ℝ))
            - G x (EuclideanSpace.single i (1 : ℝ))‖) p volume :=
        eLpNorm_sum_le (fun i _ => (hD i).norm) hp
    _ = ∑ i, eLpNorm (fun x => F x (EuclideanSpace.single i (1 : ℝ))
            - G x (EuclideanSpace.single i (1 : ℝ))) p volume := by simp_rw [eLpNorm_norm]

end Sobolev

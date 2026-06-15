import MyProject.Sobolev
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.Calculus.BumpFunction.Convolution

open MeasureTheory InnerProductSpace Set Topology Filter ContinuousLinearMap
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

/-- An `Lᵖ` bound for a function supported in a set `L` and bounded in norm:
`‖f‖_p ≤ (vol L)^{1/p} · C`. -/
lemma eLpNorm_le_of_support_subset {f : ℝⁿ → ℝ} {L : Set ℝⁿ}
    (hsupp : Function.support f ⊆ L) {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) {p : ℝ≥0∞} :
    eLpNorm f p volume ≤ (volume L) ^ (p.toReal⁻¹) * ENNReal.ofReal C := by
  rw [← eLpNorm_restrict_eq_of_support_subset hsupp]
  calc eLpNorm f p (volume.restrict L)
      ≤ (volume.restrict L) Set.univ ^ (p.toReal⁻¹) * ENNReal.ofReal C :=
        eLpNorm_le_of_ae_bound (Filter.Eventually.of_forall hC)
    _ = (volume L) ^ (p.toReal⁻¹) * ENNReal.ofReal C := by rw [Measure.restrict_apply_univ]

/-- **Translation is `Lᵖ`-continuous for continuous, compactly supported functions.** -/
lemma tendsto_eLpNorm_translate_sub_continuous {g : ℝⁿ → ℝ}
    (hg : Continuous g) (h2g : HasCompactSupport g) {p : ℝ≥0∞} :
    Tendsto (fun t : ℝⁿ => eLpNorm (fun x => g (x + t) - g x) p volume) (𝓝 0) (𝓝 0) := by
  have hunif : UniformContinuous g :=
    hg.uniformContinuous_of_tendsto_cocompact (h2g.is_zero_at_infty)
  -- a fixed compact set containing all the relevant supports (for `‖t‖ < 1`)
  set L : Set ℝⁿ := Metric.cthickening 1 (tsupport g) with hLdef
  have hLc : IsCompact L := IsCompact.cthickening h2g
  set cV : ℝ≥0∞ := (volume L) ^ (p.toReal⁻¹) with hcV
  have hcV_ne : cV ≠ (⊤ : ℝ≥0∞) :=
    ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)
      (ne_of_lt hLc.measure_lt_top)
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  rcases eq_or_ne ε ∞ with rfl | hε_top
  · exact Eventually.of_forall fun t => le_top
  -- pick a real modulus `η > 0` with `cV · ofReal η ≤ ε`
  have hcV1 : cV + 1 ≠ 0 := (lt_of_lt_of_le zero_lt_one le_add_self).ne'
  have hcV1_top : cV + 1 ≠ (⊤ : ℝ≥0∞) := ENNReal.add_ne_top.mpr ⟨hcV_ne, ENNReal.one_ne_top⟩
  obtain ⟨η, hη_pos, hη_le⟩ : ∃ η : ℝ, 0 < η ∧ cV * ENNReal.ofReal η ≤ ε := by
    have hdiv_top : ε / (cV + 1) ≠ (⊤ : ℝ≥0∞) := ENNReal.div_ne_top hε_top hcV1
    refine ⟨(ε / (cV + 1)).toReal, ?_, ?_⟩
    · have hne : ε / (cV + 1) ≠ 0 := ENNReal.div_ne_zero.mpr ⟨hε.ne', hcV1_top⟩
      exact ENNReal.toReal_pos hne hdiv_top
    · rw [ENNReal.ofReal_toReal hdiv_top]
      calc cV * (ε / (cV + 1)) ≤ (cV + 1) * (ε / (cV + 1)) := by gcongr; exact le_self_add
        _ = ε := ENNReal.mul_div_cancel hcV1 hcV1_top
  -- uniform continuity threshold; also force `‖t‖ < 1`
  obtain ⟨δ, hδ_pos, hδ⟩ := Metric.uniformContinuous_iff.mp hunif η hη_pos
  filter_upwards [Metric.ball_mem_nhds (0 : ℝⁿ) (lt_min hδ_pos one_pos)] with t ht
  rw [Metric.mem_ball, dist_eq_norm, sub_zero] at ht
  have ht_δ : ‖t‖ < δ := lt_of_lt_of_le ht (min_le_left _ _)
  have ht_1 : ‖t‖ < 1 := lt_of_lt_of_le ht (min_le_right _ _)
  refine (eLpNorm_le_of_support_subset ?_ ?_).trans hη_le
  · -- support of the difference lies in `L`
    refine (Function.support_sub _ _).trans (union_subset ?_ ?_)
    · intro x hx
      have hxt : x + t ∈ tsupport g := subset_tsupport _ (by simpa using hx)
      refine Metric.mem_cthickening_of_dist_le x (x + t) 1 (tsupport g) hxt ?_
      rw [dist_eq_norm, show x - (x + t) = -t by abel, norm_neg]
      exact ht_1.le
    · exact (subset_tsupport _).trans (Metric.self_subset_cthickening _)
  · intro x
    have hd : dist (x + t) x < δ := by rw [dist_eq_norm]; simpa using ht_δ
    have := hδ hd
    rw [dist_eq_norm] at this
    exact this.le

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

/-- **Weighted power-mean (Jensen) inequality** in `ℝ≥0∞`: for a probability weight `w`
(`∫⁻ w = 1`, finite) and `P ≥ 1`, `(∫⁻ w·h)^P ≤ ∫⁻ w·h^P`.  Derived from Hölder's inequality. -/
lemma rpow_lintegral_weighted_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {w h : α → ℝ≥0∞} (hw : AEMeasurable w μ) (hh : AEMeasurable h μ)
    (hw_top : ∀ y, w y ≠ ⊤) (hw1 : ∫⁻ y, w y ∂μ = 1) {P : ℝ} (hP : 1 ≤ P) :
    (∫⁻ y, w y * h y ∂μ) ^ P ≤ ∫⁻ y, w y * h y ^ P ∂μ := by
  rcases eq_or_lt_of_le hP with hP1 | hP1
  · simp [← hP1]
  have hP0 : 0 < P := lt_trans one_pos hP1
  have hPq : P.HolderConjugate (Real.conjExponent P) := Real.HolderConjugate.conjExponent hP1
  set q := Real.conjExponent P with hqdef
  have hq0 : 0 < q := hPq.symm.pos
  have hsum : 1 / q + 1 / P = 1 := by rw [one_div, one_div, add_comm]; exact hPq.inv_add_inv_eq_one
  -- factor  w·h = w^{1/q} · (w^{1/P}·h)
  have hsplit : (fun y => w y * h y) = fun y => w y ^ (1 / q) * (w y ^ (1 / P) * h y) := by
    funext y
    rcases eq_or_ne (w y) 0 with hw0 | hw0
    · rw [hw0, ENNReal.zero_rpow_of_pos (by positivity), ENNReal.zero_rpow_of_pos (by positivity)]
      simp
    · rw [← mul_assoc, ← ENNReal.rpow_add _ _ hw0 (hw_top y), hsum, ENNReal.rpow_one]
  have hmw : AEMeasurable (fun y => w y ^ (1 / q)) μ :=
    (ENNReal.continuous_rpow_const (y := 1 / q)).measurable.comp_aemeasurable hw
  have hmg : AEMeasurable (fun y => w y ^ (1 / P) * h y) μ :=
    ((ENNReal.continuous_rpow_const (y := 1 / P)).measurable.comp_aemeasurable hw).mul hh
  have hfq : ∫⁻ y, (w y ^ (1 / q)) ^ q ∂μ = 1 := by
    rw [← hw1]; refine lintegral_congr fun y => ?_
    rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hq0.ne', ENNReal.rpow_one]
  have hgP : ∫⁻ y, (w y ^ (1 / P) * h y) ^ P ∂μ = ∫⁻ y, w y * h y ^ P ∂μ := by
    refine lintegral_congr fun y => ?_
    rw [ENNReal.mul_rpow_of_nonneg _ _ hP0.le, ← ENNReal.rpow_mul, one_div,
      inv_mul_cancel₀ hP0.ne', ENNReal.rpow_one]
  -- Hölder with exponents q (for `w^{1/q}`) and P (for `w^{1/P}·h`)
  have hol := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hPq.symm hmw hmg
  rw [hfq, hgP, ENNReal.one_rpow, one_mul] at hol
  calc (∫⁻ y, w y * h y ∂μ) ^ P
      = (∫⁻ y, w y ^ (1 / q) * (w y ^ (1 / P) * h y) ∂μ) ^ P := by rw [hsplit]
    _ ≤ ((∫⁻ y, w y * h y ^ P ∂μ) ^ (1 / P)) ^ P := ENNReal.rpow_le_rpow hol hP0.le
    _ = ∫⁻ y, w y * h y ^ P ∂μ := by
        rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hP0.ne', ENNReal.rpow_one]

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
        show v t * φ t = η (x - t) * v t
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

end Sobolev

import MyProject.Sobolev
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.Calculus.BumpFunction.Convolution

open MeasureTheory InnerProductSpace Set Topology Filter
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

end Sobolev

import MyProject.Mollification

open MeasureTheory InnerProductSpace Set Topology intervalIntegral
open scoped ContDiff ENNReal NNReal

/-!
# Towards the Rellich–Kondrachov compactness theorem (Evans §5.7)

The Rellich–Kondrachov theorem states that for a bounded open set `U`, the embedding
`W^{1,p}(U) ↪ L^q(U)` is **compact** for `1 ≤ q < p*`.  Unlike the Sobolev embedding and Poincaré
inequalities (which specialize directly from Mathlib's Gagliardo–Nirenberg–Sobolev inequality),
Rellich rests on a compactness criterion that Mathlib does **not** yet provide:

* **Fréchet–Kolmogorov / Riesz** — a bounded subset of `Lᵖ` that is uniformly tight and uniformly
  `Lᵖ`-translation-equicontinuous is precompact.  (Mathlib has Arzelà–Ascoli for continuous maps,
  but not the `Lᵖ`-precompactness criterion.)

This file builds the analytic inputs to that program, starting from the bottom.

## Roadmap

1. **`sub_eq_integral_fderiv_segment`** (done): the fundamental theorem of calculus along a
   segment, `u(x+h) − u(x) = ∫₀¹ Du(x+t·h)[h] dt`.
2. **Translation estimate** (next): `‖u(·+h) − u‖_p ≤ |h| · ‖Du‖_p`, the quantitative
   `Lᵖ`-modulus-of-continuity bound that supplies the equicontinuity hypothesis of
   Fréchet–Kolmogorov.  Proved from (1) by the weighted-Jensen + Tonelli + translation-invariance
   technique of `eLpNorm_convolution_sub_rpow_le` (avoiding Minkowski's integral inequality, which
   Mathlib also lacks).
3. **Fréchet–Kolmogorov precompactness** (large): mollify the family, get equicontinuity and
   uniform bounds, apply Arzelà–Ascoli, and assemble total boundedness.
4. **Rellich–Kondrachov**: combine (2)+(3) with the Sobolev embedding.
-/

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

namespace Sobolev

/-- **Fundamental theorem of calculus along the segment** from `x` to `x + h`:
`u(x+h) - u(x) = ∫₀¹ Du(x + t·h)[h] dt`.  The map `t ↦ u(x + t·h)` has derivative
`Du(x + t·h)[h]` (chain rule), and its directional derivative is continuous, so the FTC applies. -/
lemma sub_eq_integral_fderiv_segment {u : ℝⁿ → ℝ} (hu : ContDiff ℝ 1 u) (x h : ℝⁿ) :
    u (x + h) - u x = ∫ t in (0:ℝ)..1, fderiv ℝ u (x + t • h) h := by
  have hφderiv : ∀ t : ℝ, HasDerivAt (fun t => x + t • h) h t := fun t => by
    simpa using (((hasDerivAt_id t).smul_const h).const_add x)
  have hg : ∀ t : ℝ, HasDerivAt (fun s => u (x + s • h)) (fderiv ℝ u (x + t • h) h) t := by
    intro t
    have hfd : HasFDerivAt u (fderiv ℝ u (x + t • h)) (x + t • h) :=
      (hu.differentiable one_ne_zero (x + t • h)).hasFDerivAt
    exact hfd.comp_hasDerivAt t (hφderiv t)
  have hcont : Continuous (fun t : ℝ => fderiv ℝ u (x + t • h) h) := by
    have h1 : Continuous (fun y : ℝⁿ => fderiv ℝ u y h) :=
      (hu.continuous_fderiv one_ne_zero).clm_apply continuous_const
    exact h1.comp (continuous_const.add (continuous_id.smul continuous_const))
  have hint : IntervalIntegrable (fun t => fderiv ℝ u (x + t • h) h) volume 0 1 :=
    hcont.intervalIntegrable 0 1
  have key := integral_eq_sub_of_hasDerivAt (fun t _ => hg t) hint
  simp only [one_smul, zero_smul, add_zero] at key
  exact key.symm

/-- Pointwise `enorm` bound from the segment FTC: the increment to the power `P` is controlled by
the average of the `P`-th power of the gradient norm along the segment (weighted Jensen). -/
lemma enorm_sub_translate_rpow_le {u : ℝⁿ → ℝ} (hu : ContDiff ℝ 1 u) (h : ℝⁿ) {P : ℝ}
    (hP : 1 ≤ P) (x : ℝⁿ) :
    ‖u (x + h) - u x‖ₑ ^ P
      ≤ ∫⁻ t in Set.Icc (0:ℝ) 1, (‖fderiv ℝ u (x + t • h)‖ₑ * ‖h‖ₑ) ^ P ∂volume := by
  have hP0 : 0 < P := lt_of_lt_of_le one_pos hP
  set μ : Measure ℝ := volume.restrict (Set.Icc (0:ℝ) 1) with hμ
  have hμ1 : ∫⁻ _ : ℝ, (1 : ℝ≥0∞) ∂μ = 1 := by
    rw [lintegral_one, hμ, Measure.restrict_apply_univ, Real.volume_Icc]; simp
  have hcont2 : Continuous (fun t : ℝ => fderiv ℝ u (x + t • h)) :=
    (hu.continuous_fderiv one_ne_zero).comp
      (continuous_const.add (continuous_id.smul continuous_const))
  have hmeas : AEMeasurable (fun t : ℝ => ‖fderiv ℝ u (x + t • h)‖ₑ * ‖h‖ₑ) μ :=
    hcont2.enorm.aemeasurable.mul aemeasurable_const
  have hbd : ∀ t : ℝ, ‖fderiv ℝ u (x + t • h) h‖ₑ ≤ ‖fderiv ℝ u (x + t • h)‖ₑ * ‖h‖ₑ := by
    intro t
    rw [enorm_eq_nnnorm, enorm_eq_nnnorm, enorm_eq_nnnorm, ← ENNReal.coe_mul, ENNReal.coe_le_coe]
    exact (fderiv ℝ u (x + t • h)).le_opNNNorm h
  have htri : ‖u (x + h) - u x‖ₑ ≤ ∫⁻ t, ‖fderiv ℝ u (x + t • h) h‖ₑ ∂μ := by
    rw [sub_eq_integral_fderiv_segment hu x h,
      intervalIntegral.intervalIntegral_eq_integral_uIoc, if_pos (by norm_num : (0:ℝ) ≤ 1),
      one_smul, Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    refine le_trans (enorm_integral_le_lintegral_enorm _) ?_
    exact lintegral_mono_set Set.Ioc_subset_Icc_self
  have htri2 : ‖u (x + h) - u x‖ₑ ≤ ∫⁻ t, ‖fderiv ℝ u (x + t • h)‖ₑ * ‖h‖ₑ ∂μ :=
    htri.trans (lintegral_mono hbd)
  calc ‖u (x + h) - u x‖ₑ ^ P
      ≤ (∫⁻ t, ‖fderiv ℝ u (x + t • h)‖ₑ * ‖h‖ₑ ∂μ) ^ P := ENNReal.rpow_le_rpow htri2 hP0.le
    _ ≤ ∫⁻ t, (‖fderiv ℝ u (x + t • h)‖ₑ * ‖h‖ₑ) ^ P ∂μ := by
        have := rpow_lintegral_weighted_le (μ := μ) (w := fun _ => (1 : ℝ≥0∞))
          (h := fun t => ‖fderiv ℝ u (x + t • h)‖ₑ * ‖h‖ₑ)
          aemeasurable_const hmeas (fun _ => ENNReal.one_ne_top) hμ1 hP
        simpa using this

/-- **Translation (modulus-of-continuity) estimate.** For a `C¹` function `u` and `1 ≤ p < ∞`, the
`Lᵖ` distance between `u` and its translate is controlled by the displacement times the `Lᵖ` norm of
the gradient: `‖u(·+h) − u‖_p ≤ |h| · ‖Du‖_p`. This is the equicontinuity input to the
Fréchet–Kolmogorov compactness criterion. Proved from the segment FTC by weighted Jensen
(`enorm_sub_translate_rpow_le`), Tonelli, and translation-invariance of the Lebesgue integral —
avoiding Minkowski's integral inequality. -/
theorem eLpNorm_translate_sub_le_fderiv {u : ℝⁿ → ℝ} (hu : ContDiff ℝ 1 u)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (h : ℝⁿ) :
    eLpNorm (fun x => u (x + h) - u x) p volume
      ≤ ‖h‖ₑ * eLpNorm (fun x => fderiv ℝ u x) p volume := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hp0 : p ≠ 0 := fun hpe => by simp [hpe] at hp1
  have hP1 : 1 ≤ p.toReal := by
    rw [show (1 : ℝ) = (1 : ℝ≥0∞).toReal from ENNReal.toReal_one.symm]
    exact ENNReal.toReal_mono hp hp1
  have hP0 : 0 < p.toReal := lt_of_lt_of_le one_pos hP1
  set P := p.toReal with hPdef
  have hgcont : Continuous (fun y : ℝⁿ => fderiv ℝ u y) := hu.continuous_fderiv one_ne_zero
  -- joint measurability of the product integrand
  have hjoint : AEMeasurable
      (Function.uncurry fun x t => (‖fderiv ℝ u (x + t • h)‖ₑ * ‖h‖ₑ) ^ P)
      (volume.prod (volume.restrict (Set.Icc (0:ℝ) 1))) := by
    have hc : Continuous fun q : ℝⁿ × ℝ => fderiv ℝ u (q.1 + q.2 • h) :=
      hgcont.comp (continuous_fst.add (continuous_snd.smul continuous_const))
    have hg_meas : Measurable fun q : ℝⁿ × ℝ => ‖fderiv ℝ u (q.1 + q.2 • h)‖ₑ * ‖h‖ₑ :=
      hc.enorm.measurable.mul measurable_const
    exact ((ENNReal.continuous_rpow_const (y := P)).measurable.comp hg_meas).aemeasurable
  -- per-slice translation invariance: `∫⁻ x, ‖∂u(x+t·h)‖^P = (eLpNorm Du p)^P`
  have hslice : ∀ t : ℝ, ∫⁻ x, (‖fderiv ℝ u (x + t • h)‖ₑ * ‖h‖ₑ) ^ P ∂volume
      = ‖h‖ₑ ^ P * (eLpNorm (fun x => fderiv ℝ u x) p volume) ^ P := by
    intro t
    have htrans : ∫⁻ x, ‖fderiv ℝ u (x + t • h)‖ₑ ^ P ∂volume
        = ∫⁻ x, ‖fderiv ℝ u x‖ₑ ^ P ∂volume :=
      lintegral_add_right_eq_self (fun y => ‖fderiv ℝ u y‖ₑ ^ P) (t • h)
    calc ∫⁻ x, (‖fderiv ℝ u (x + t • h)‖ₑ * ‖h‖ₑ) ^ P ∂volume
        = ∫⁻ x, ‖h‖ₑ ^ P * ‖fderiv ℝ u (x + t • h)‖ₑ ^ P ∂volume := by
          refine lintegral_congr fun x => ?_
          rw [ENNReal.mul_rpow_of_nonneg _ _ hP0.le, mul_comm]
      _ = ‖h‖ₑ ^ P * ∫⁻ x, ‖fderiv ℝ u (x + t • h)‖ₑ ^ P ∂volume :=
          lintegral_const_mul' _ _ (by finiteness)
      _ = ‖h‖ₑ ^ P * ∫⁻ x, ‖fderiv ℝ u x‖ₑ ^ P ∂volume := by rw [htrans]
      _ = ‖h‖ₑ ^ P * (eLpNorm (fun x => fderiv ℝ u x) p volume) ^ P := by
          rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp, ← ENNReal.rpow_mul, one_div,
            inv_mul_cancel₀ hP0.ne', ENNReal.rpow_one]
  -- assemble
  have hkey : (eLpNorm (fun x => u (x + h) - u x) p volume) ^ P
      ≤ (‖h‖ₑ * eLpNorm (fun x => fderiv ℝ u x) p volume) ^ P := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp, ← ENNReal.rpow_mul, one_div,
      inv_mul_cancel₀ hP0.ne', ENNReal.rpow_one]
    calc ∫⁻ x, ‖u (x + h) - u x‖ₑ ^ P ∂volume
        ≤ ∫⁻ x, ∫⁻ t in Set.Icc (0:ℝ) 1, (‖fderiv ℝ u (x + t • h)‖ₑ * ‖h‖ₑ) ^ P ∂volume
            ∂volume := lintegral_mono fun x => enorm_sub_translate_rpow_le hu h hP1 x
      _ = ∫⁻ t in Set.Icc (0:ℝ) 1, ∫⁻ x, (‖fderiv ℝ u (x + t • h)‖ₑ * ‖h‖ₑ) ^ P ∂volume
            ∂volume := lintegral_lintegral_swap hjoint
      _ = ∫⁻ t in Set.Icc (0:ℝ) 1, ‖h‖ₑ ^ P
            * (eLpNorm (fun x => fderiv ℝ u x) p volume) ^ P ∂volume :=
          lintegral_congr fun t => hslice t
      _ = ‖h‖ₑ ^ P * (eLpNorm (fun x => fderiv ℝ u x) p volume) ^ P := by
          rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc]; simp
      _ = (‖h‖ₑ * eLpNorm (fun x => fderiv ℝ u x) p volume) ^ P := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hP0.le]
  -- take `p`-th roots
  have := ENNReal.rpow_le_rpow hkey (by positivity : (0:ℝ) ≤ 1 / P)
  rwa [← ENNReal.rpow_mul, ← ENNReal.rpow_mul, mul_one_div, div_self hP0.ne',
    ENNReal.rpow_one, ENNReal.rpow_one] at this

end Sobolev


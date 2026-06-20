import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Weighted power-mean (Jensen) inequality in `ℝ≥0∞`

A single lightweight lemma factored out of `Mollification.lean` so that downstream files (notably
`Rellich.lean`) can use it without importing the heavy `SobolevInequality` / `Convolution` chain.
-/

open MeasureTheory
open scoped ENNReal

namespace Sobolev

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

import MyProject.LpJensen
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
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

end Sobolev

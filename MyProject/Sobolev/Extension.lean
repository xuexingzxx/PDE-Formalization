import MyProject.Sobolev.Basic

/-!
# Sobolev extension operator (Evans §5.4) — foundations

The extension theorem builds a bounded linear operator `E : W^{1,p}(Ω) → W^{1,p}(ℝⁿ)` extending
functions off a bounded `C¹` domain, by reflecting across a (locally flattened) boundary.  This file
begins with the local engine: the **reflection across the coordinate hyperplane `{xᵢ = 0}`**, packaged
as a linear isometry equivalence so that smoothness, involutivity and measure-preservation are all
available for the reflection-extension estimate that follows.
-/

open MeasureTheory
open scoped RealInnerProductSpace

namespace Sobolev

variable {n : ℕ}
local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- The linear reflection of `ℝⁿ` across the hyperplane `{xᵢ = 0}`: it negates the `i`-th coordinate
and fixes the others, `x ↦ x - 2·xᵢ·eᵢ`. -/
noncomputable def reflLin (i : Fin n) : ℝⁿ →ₗ[ℝ] ℝⁿ where
  toFun x := x - (2 * x i) • EuclideanSpace.single i (1 : ℝ)
  map_add' x y := by
    ext j
    rcases eq_or_ne j i with rfl | hj
    · simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, EuclideanSpace.single_apply,
        if_pos rfl, smul_eq_mul, mul_one]; ring
    · simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, EuclideanSpace.single_apply,
        if_neg hj, smul_eq_mul, mul_zero, sub_zero]
  map_smul' c x := by
    ext j
    rcases eq_or_ne j i with rfl | hj
    · simp only [PiLp.smul_apply, PiLp.sub_apply, EuclideanSpace.single_apply, if_pos rfl,
        smul_eq_mul, mul_one, RingHom.id_apply]; ring
    · simp only [PiLp.smul_apply, PiLp.sub_apply, EuclideanSpace.single_apply, if_neg hj,
        smul_eq_mul, mul_zero, sub_zero, RingHom.id_apply]

/-- `reflLin` negates the `i`-th coordinate. -/
@[simp] theorem reflLin_apply_self (i : Fin n) (x : ℝⁿ) : reflLin i x i = - x i := by
  simp [reflLin, PiLp.sub_apply, PiLp.smul_apply, EuclideanSpace.single_apply]; ring

/-- `reflLin` fixes the other coordinates. -/
theorem reflLin_apply_of_ne (i : Fin n) (x : ℝⁿ) {j : Fin n} (hj : j ≠ i) :
    reflLin i x j = x j := by
  simp only [reflLin, LinearMap.coe_mk, AddHom.coe_mk, PiLp.sub_apply, PiLp.smul_apply,
    EuclideanSpace.single_apply, if_neg hj, smul_eq_mul, mul_zero, sub_zero]

/-- The reflection is an involution. -/
theorem reflLin_involutive (i : Fin n) : Function.Involutive (reflLin i) := by
  intro x
  ext j
  rcases eq_or_ne j i with rfl | hj
  · simp
  · rw [reflLin_apply_of_ne i _ hj, reflLin_apply_of_ne i _ hj]

/-- The reflection preserves the Euclidean norm (it flips the sign of one orthonormal coordinate). -/
theorem reflLin_norm (i : Fin n) (x : ℝⁿ) : ‖reflLin i x‖ = ‖x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rcases eq_or_ne j i with rfl | hj
  · rw [reflLin_apply_self]; simp [abs_neg]
  · rw [reflLin_apply_of_ne i _ hj]

/-- The reflection of `ℝⁿ` across `{xᵢ = 0}`, as a linear isometry equivalence. -/
noncomputable def refll (i : Fin n) : ℝⁿ ≃ₗᵢ[ℝ] ℝⁿ where
  toLinearEquiv := LinearEquiv.ofLinear (reflLin i) (reflLin i)
    (LinearMap.ext fun x => reflLin_involutive i x) (LinearMap.ext fun x => reflLin_involutive i x)
  norm_map' := reflLin_norm i

@[simp] theorem refll_apply (i : Fin n) (x : ℝⁿ) : refll i x = reflLin i x := rfl

/-- The reflection is smooth (it is linear). -/
theorem contDiff_refll (i : Fin n) : ContDiff ℝ (⊤ : ℕ∞) (refll i) :=
  (refll i).toContinuousLinearEquiv.contDiff

/-- The reflection preserves Lebesgue measure. -/
theorem refll_measurePreserving (i : Fin n) :
    MeasurePreserving (refll i) (volume : Measure ℝⁿ) volume :=
  (refll i).measurePreserving

/-- The reflection negates `eᵢ` and fixes `eⱼ` for `j ≠ i`. -/
theorem refll_single (i j : Fin n) :
    refll i (EuclideanSpace.single j (1 : ℝ))
      = (if j = i then (-1 : ℝ) else 1) • EuclideanSpace.single j (1 : ℝ) := by
  simp only [refll_apply, reflLin, LinearMap.coe_mk, AddHom.coe_mk]
  rcases eq_or_ne j i with rfl | hji
  · rw [if_pos rfl,
      show (EuclideanSpace.single j (1 : ℝ)) j = 1 from by simp [PiLp.single_apply]]
    module
  · rw [if_neg hji, one_smul,
      show (EuclideanSpace.single j (1 : ℝ)) i = 0 from by
        simp [PiLp.single_apply, Ne.symm hji]]
    module

/-- The `i`-th coordinate of the reflection is the negation. -/
@[simp] theorem refll_apply_self (i : Fin n) (x : ℝⁿ) : (refll i x) i = - x i :=
  reflLin_apply_self i x

/-- The reflection is an involution. -/
theorem refll_involutive (i : Fin n) : Function.Involutive (refll i) := reflLin_involutive i

/-- The reflection swaps the two open half-spaces: `refll i '' {xᵢ > 0} = {xᵢ < 0}`. -/
theorem refll_image_upper (i : Fin n) :
    refll i '' {x : ℝⁿ | 0 < x i} = {x : ℝⁿ | x i < 0} := by
  ext y
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, hx, rfl⟩; rw [refll_apply_self]; linarith
  · intro hy
    exact ⟨refll i y, by rw [refll_apply_self]; linarith, refll_involutive i y⟩

end Sobolev

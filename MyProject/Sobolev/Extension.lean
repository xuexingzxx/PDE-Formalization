import MyProject.Sobolev.Basic

/-!
# Sobolev extension operator (Evans §5.4) — foundations

The extension theorem builds a bounded linear operator `E : W^{1,p}(Ω) → W^{1,p}(ℝⁿ)` extending
functions off a bounded `C¹` domain, by reflecting across a (locally flattened) boundary.  This file
begins with the local engine: the **reflection across the coordinate hyperplane `{xᵢ = 0}`**,
packaged as a linear isometry equivalence so that smoothness, involutivity and measure-preservation
are all available for the reflection-extension estimate that follows.
-/

open MeasureTheory
open scoped RealInnerProductSpace ContDiff

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
    · simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.single_apply,
        smul_eq_mul]; ring
    · simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.single_apply,
        if_neg hj, smul_eq_mul, mul_zero, sub_zero]
  map_smul' c x := by
    ext j
    rcases eq_or_ne j i with rfl | hj
    · simp only [PiLp.smul_apply, PiLp.sub_apply, PiLp.single_apply,
        smul_eq_mul, RingHom.id_apply]; ring
    · simp only [PiLp.smul_apply, PiLp.sub_apply, PiLp.single_apply, if_neg hj,
        smul_eq_mul, mul_zero, sub_zero, RingHom.id_apply]

/-- `reflLin` negates the `i`-th coordinate. -/
@[simp] theorem reflLin_apply_self (i : Fin n) (x : ℝⁿ) : reflLin i x i = - x i := by
  simp [reflLin, PiLp.sub_apply, PiLp.smul_apply]; ring

/-- `reflLin` fixes the other coordinates. -/
theorem reflLin_apply_of_ne (i : Fin n) (x : ℝⁿ) {j : Fin n} (hj : j ≠ i) :
    reflLin i x j = x j := by
  simp only [reflLin, LinearMap.coe_mk, AddHom.coe_mk, PiLp.sub_apply, PiLp.smul_apply,
    PiLp.single_apply, if_neg hj, smul_eq_mul, mul_zero, sub_zero]

/-- The reflection is an involution. -/
theorem reflLin_involutive (i : Fin n) : Function.Involutive (reflLin i) := by
  intro x
  ext j
  rcases eq_or_ne j i with rfl | hj
  · simp
  · rw [reflLin_apply_of_ne i _ hj, reflLin_apply_of_ne i _ hj]

/-- The reflection preserves the Euclidean norm (it flips the sign of one coordinate). -/
theorem reflLin_norm (i : Fin n) (x : ℝⁿ) : ‖reflLin i x‖ = ‖x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rcases eq_or_ne j i with rfl | hj
  · rw [reflLin_apply_self]; simp
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
      show (EuclideanSpace.single j (1 : ℝ)) j = 1 from by simp]
    module
  · rw [if_neg hji, one_smul,
      show (EuclideanSpace.single j (1 : ℝ)) i = 0 from by
        simp [Ne.symm hji]]
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

/-- The reflection is a measurable embedding (it is a homeomorphism). -/
theorem refll_measurableEmbedding (i : Fin n) : MeasurableEmbedding (refll i) :=
  (refll i).toHomeomorph.measurableEmbedding

/-- **Reflection change-of-variables for weak derivatives.** If `v` is the weak `eⱼ`-derivative of
`u` on the open upper half-space `{xᵢ > 0}`, then the reflected function `u ∘ refll i` has the
sign-adjusted reflected weak `eⱼ`-derivative on the open lower half-space `{xᵢ < 0}`: the sign is
`-1` in the reflected direction `j = i` and `+1` otherwise.  This is the first analytic ingredient
of the reflection-extension estimate (Evans §5.4): the substitution `x = refll i y`, which preserves
Lebesgue measure, together with the chain rule `∂ⱼ(φ ∘ refll i) = ±∂ⱼφ ∘ refll i`, transports the
upper-half integration-by-parts identity to the lower half. -/
theorem isWeakDerivInDir_comp_refll (i j : Fin n) {u v : ℝⁿ → ℝ}
    (h : IsWeakDerivInDir {x : ℝⁿ | 0 < x i} (EuclideanSpace.single j (1 : ℝ)) u v) :
    IsWeakDerivInDir {x : ℝⁿ | x i < 0} (EuclideanSpace.single j (1 : ℝ))
      (fun x => u (refll i x))
      (fun x => (if j = i then (-1 : ℝ) else 1) * v (refll i x)) := by
  intro φ hφ
  have hinv : ∀ x, refll i (refll i x) = x := refll_involutive i
  have hsgn2 : (if j = i then (-1 : ℝ) else 1) * (if j = i then (-1 : ℝ) else 1) = 1 := by
    split_ifs <;> ring
  -- `ψ = φ ∘ refll i` is a test function on the upper half-space.
  have hψcd : ContDiff ℝ ∞ (fun z => φ (refll i z)) := hφ.contDiff.comp (contDiff_refll i)
  have hψcs : HasCompactSupport (fun z => φ (refll i z)) :=
    hφ.hasCompactSupport.comp_homeomorph (refll i).toHomeomorph
  have hψts : tsupport (fun z => φ (refll i z)) ⊆ {x : ℝⁿ | 0 < x i} := by
    have hgeq : (fun z => φ (refll i z)) = φ ∘ (⇑(refll i).toHomeomorph) := rfl
    rw [hgeq, tsupport_comp_eq_preimage]
    intro y hy
    have hy' : refll i y ∈ tsupport φ := hy
    have hmem := hφ.tsupport_subset hy'
    simp only [Set.mem_setOf_eq, refll_apply_self] at hmem ⊢
    linarith
  have hψ : IsTestFunction {x : ℝⁿ | 0 < x i} (fun z => φ (refll i z)) := ⟨hψcd, hψcs, hψts⟩
  -- Pointwise chain-rule identity relating `∂ⱼφ` at `refll i y` to `∂ⱼ(φ ∘ refll i)` at `y`.
  have hpt : ∀ y, fderiv ℝ φ (refll i y) (EuclideanSpace.single j (1 : ℝ))
      = (if j = i then (-1 : ℝ) else 1)
        * fderiv ℝ (fun z => φ (refll i z)) y (EuclideanSpace.single j (1 : ℝ)) := by
    intro y
    have hcomp : HasFDerivAt (fun z => φ (refll i z))
        ((fderiv ℝ φ (refll i y)).comp ((refll i).toContinuousLinearEquiv : ℝⁿ →L[ℝ] ℝⁿ)) y :=
      (hφ.differentiable (refll i y)).hasFDerivAt.comp y
        (refll i).toContinuousLinearEquiv.hasFDerivAt
    have hA : fderiv ℝ (fun z => φ (refll i z)) y (EuclideanSpace.single j (1 : ℝ))
        = (if j = i then (-1 : ℝ) else 1)
          * fderiv ℝ φ (refll i y) (EuclideanSpace.single j (1 : ℝ)) := by
      rw [hcomp.fderiv, ContinuousLinearMap.comp_apply]
      change fderiv ℝ φ (refll i y) (refll i (EuclideanSpace.single j (1 : ℝ))) = _
      rw [refll_single, map_smul, smul_eq_mul]
    rw [hA, ← mul_assoc, hsgn2, one_mul]
  -- Change variables `x = refll i y` on both sides using measure-preservation of the reflection.
  have hcovL : ∫ x, u (refll i x) * fderiv ℝ φ x (EuclideanSpace.single j (1 : ℝ))
      = ∫ y, u y * fderiv ℝ φ (refll i y) (EuclideanSpace.single j (1 : ℝ)) := by
    have key := (refll_measurePreserving i).integral_comp (refll_measurableEmbedding i)
      (fun y => u y * fderiv ℝ φ (refll i y) (EuclideanSpace.single j (1 : ℝ)))
    simp only [hinv] at key
    exact key
  have hcovR : ∫ x, ((if j = i then (-1 : ℝ) else 1) * v (refll i x)) * φ x
      = (if j = i then (-1 : ℝ) else 1) * ∫ y, v y * φ (refll i y) := by
    have key := (refll_measurePreserving i).integral_comp (refll_measurableEmbedding i)
      (fun y => ((if j = i then (-1 : ℝ) else 1) * v y) * φ (refll i y))
    simp only [hinv] at key
    rw [key, ← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun x => by ring))
  -- Assemble: transport to the upper half, apply the hypothesis, transport back.
  rw [hcovL]
  have hrw : ∫ y, u y * fderiv ℝ φ (refll i y) (EuclideanSpace.single j (1 : ℝ))
      = (if j = i then (-1 : ℝ) else 1)
        * ∫ y, u y * fderiv ℝ (fun z => φ (refll i z)) y (EuclideanSpace.single j (1 : ℝ)) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    dsimp only
    rw [hpt y]; ring
  rw [hrw, h _ hψ, hcovR]
  ring

end Sobolev

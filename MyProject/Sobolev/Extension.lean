import MyProject.Sobolev.Basic
import MyProject.Sobolev.Mollification

/-!
# Sobolev extension operator (Evans §5.4) — foundations

The extension theorem builds a bounded linear operator `E : W^{1,p}(Ω) → W^{1,p}(ℝⁿ)` extending
functions off a bounded `C¹` domain, by reflecting across a (locally flattened) boundary.  This file
begins with the local engine: the **reflection across the coordinate hyperplane `{xᵢ = 0}`**,
packaged as a linear isometry equivalence so that smoothness, involutivity and measure-preservation
are all available for the reflection-extension estimate that follows.
-/

open MeasureTheory Filter
open scoped RealInnerProductSpace ContDiff Topology ENNReal Convolution

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


/-- Smooth one-sided cutoff in the `i`-th coordinate: `0` where `x i ≤ 1/(m+1)`, `1` where
`x i ≥ 2/(m+1)`, values in `[0,1]`. -/
noncomputable def cutoffPos (i : Fin n) (m : ℕ) (x : ℝⁿ) : ℝ :=
  Real.smoothTransition ((m + 1 : ℝ) * x i - 1)

theorem cutoffPos_contDiff (i : Fin n) (m : ℕ) : ContDiff ℝ ∞ (cutoffPos i m) :=
  Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul (EuclideanSpace.proj i : ℝⁿ →L[ℝ] ℝ).contDiff).sub contDiff_const)

theorem cutoffPos_nonneg (i : Fin n) (m : ℕ) (x : ℝⁿ) : 0 ≤ cutoffPos i m x :=
  Real.smoothTransition.nonneg _

theorem cutoffPos_le_one (i : Fin n) (m : ℕ) (x : ℝⁿ) : cutoffPos i m x ≤ 1 :=
  Real.smoothTransition.le_one _

theorem cutoffPos_eq_zero (i : Fin n) (m : ℕ) {x : ℝⁿ} (hx : x i ≤ 0) : cutoffPos i m x = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have : (m + 1 : ℝ) * x i ≤ 0 := mul_nonpos_iff.2 (Or.inl ⟨by positivity, hx⟩)
  linarith

theorem cutoffPos_eq_zero_of_le (i : Fin n) (m : ℕ) {x : ℝⁿ} (hx : (m + 1 : ℝ) * x i ≤ 1) :
    cutoffPos i m x = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem cutoffPos_tendsto_one (i : Fin n) {x : ℝⁿ} (hx : 0 < x i) :
    Tendsto (fun m => cutoffPos i m x) atTop (nhds 1) := by
  apply tendsto_const_nhds.congr'
  rw [Filter.EventuallyEq, eventually_atTop]
  obtain ⟨N, hN⟩ := exists_nat_ge (2 / x i)
  refine ⟨N, fun m hm => ?_⟩
  refine (Real.smoothTransition.one_of_one_le ?_).symm
  have hxi : (0:ℝ) < x i := hx
  have : (2 : ℝ) ≤ (m + 1 : ℝ) * x i := by
    have hNle : (2 / x i) ≤ (m : ℝ) := hN.trans (by exact_mod_cast hm)
    have := (div_le_iff₀ hxi).1 hNle
    nlinarith [this]
  linarith

theorem cutoffPos_fderiv_tangential (i j : Fin n) (hji : j ≠ i) (m : ℕ) (x : ℝⁿ) :
    fderiv ℝ (cutoffPos i m) x (EuclideanSpace.single j (1 : ℝ)) = 0 := by
  have hg' : HasFDerivAt (fun y : ℝⁿ => (m + 1 : ℝ) * y i - 1)
      ((m + 1 : ℝ) • (EuclideanSpace.proj i : ℝⁿ →L[ℝ] ℝ)) x :=
    (((EuclideanSpace.proj i : ℝⁿ →L[ℝ] ℝ).hasFDerivAt).const_mul (m + 1 : ℝ)).sub_const 1
  have hF : DifferentiableAt ℝ Real.smoothTransition ((m + 1 : ℝ) * x i - 1) :=
    ((Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).differentiable (by norm_num)).differentiableAt
  have hcomp : HasFDerivAt (cutoffPos i m)
      ((fderiv ℝ Real.smoothTransition ((m + 1 : ℝ) * x i - 1)).comp
        ((m + 1 : ℝ) • (EuclideanSpace.proj i : ℝⁿ →L[ℝ] ℝ))) x :=
    hF.hasFDerivAt.comp x hg'
  rw [hcomp.fderiv, ContinuousLinearMap.comp_apply]
  have hpz : ((m + 1 : ℝ) • (EuclideanSpace.proj i : ℝⁿ →L[ℝ] ℝ))
      (EuclideanSpace.single j (1 : ℝ)) = 0 := by
    rw [ContinuousLinearMap.smul_apply]
    change (m + 1 : ℝ) • ((EuclideanSpace.single j (1 : ℝ)) i) = 0
    rw [PiLp.single_apply, if_neg (Ne.symm hji), smul_zero]
  rw [hpz, map_zero]

/-- Smooth one-sided cutoff on the **lower** half, defined by reflecting `cutoffPos`. -/
noncomputable def cutoffNeg (i : Fin n) (m : ℕ) (x : ℝⁿ) : ℝ :=
  cutoffPos i m (refll i x)

theorem cutoffNeg_contDiff (i : Fin n) (m : ℕ) : ContDiff ℝ ∞ (cutoffNeg i m) :=
  (cutoffPos_contDiff i m).comp (contDiff_refll i)

theorem cutoffNeg_nonneg (i : Fin n) (m : ℕ) (x : ℝⁿ) : 0 ≤ cutoffNeg i m x :=
  cutoffPos_nonneg i m _

theorem cutoffNeg_le_one (i : Fin n) (m : ℕ) (x : ℝⁿ) : cutoffNeg i m x ≤ 1 :=
  cutoffPos_le_one i m _

theorem cutoffNeg_eq_zero (i : Fin n) (m : ℕ) {x : ℝⁿ} (hx : 0 ≤ x i) : cutoffNeg i m x = 0 := by
  apply cutoffPos_eq_zero
  rw [refll_apply_self]; linarith

theorem cutoffNeg_tendsto_one (i : Fin n) {x : ℝⁿ} (hx : x i < 0) :
    Tendsto (fun m => cutoffNeg i m x) atTop (nhds 1) :=
  cutoffPos_tendsto_one i (x := refll i x) (by rw [refll_apply_self]; linarith)

theorem cutoffNeg_fderiv_tangential (i j : Fin n) (hji : j ≠ i) (m : ℕ) (x : ℝⁿ) :
    fderiv ℝ (cutoffNeg i m) x (EuclideanSpace.single j (1 : ℝ)) = 0 := by
  have hcomp : HasFDerivAt (cutoffNeg i m)
      ((fderiv ℝ (cutoffPos i m) (refll i x)).comp
        ((refll i).toContinuousLinearEquiv : ℝⁿ →L[ℝ] ℝⁿ)) x :=
    ((cutoffPos_contDiff i m).differentiable (by norm_num) (refll i x)).hasFDerivAt.comp x
      (refll i).toContinuousLinearEquiv.hasFDerivAt
  rw [hcomp.fderiv, ContinuousLinearMap.comp_apply]
  change fderiv ℝ (cutoffPos i m) (refll i x) (refll i (EuclideanSpace.single j (1 : ℝ))) = 0
  rw [refll_single, if_neg hji, one_smul, cutoffPos_fderiv_tangential i j hji]

/-- The coordinate hyperplane `{x | x i = 0}` is Lebesgue-null. -/
theorem volume_hyperplane_eq_zero (i : Fin n) : volume {x : ℝⁿ | x i = 0} = 0 := by
  have hker : {x : ℝⁿ | x i = 0}
      = (↑(LinearMap.ker (EuclideanSpace.projₗ i : ℝⁿ →ₗ[ℝ] ℝ)) : Set ℝⁿ) := by
    ext x
    simp only [Set.mem_setOf_eq, SetLike.mem_coe, LinearMap.mem_ker]
    rfl
  rw [hker]
  refine Measure.addHaar_submodule volume _ (fun htop => ?_)
  have h1 : (EuclideanSpace.projₗ i : ℝⁿ →ₗ[ℝ] ℝ) (EuclideanSpace.single i (1 : ℝ)) = 0 := by
    have hmem : EuclideanSpace.single i (1 : ℝ)
        ∈ LinearMap.ker (EuclideanSpace.projₗ i : ℝⁿ →ₗ[ℝ] ℝ) := by
      rw [htop]; exact Submodule.mem_top
    rwa [LinearMap.mem_ker] at hmem
  rw [show (EuclideanSpace.projₗ i : ℝⁿ →ₗ[ℝ] ℝ) (EuclideanSpace.single i (1 : ℝ))
      = (EuclideanSpace.single i (1 : ℝ)) i from rfl, PiLp.single_apply, if_pos rfl] at h1
  exact one_ne_zero h1

theorem ae_coord_ne_zero (i : Fin n) : ∀ᵐ x : ℝⁿ, x i ≠ 0 := by
  rw [ae_iff]; simpa using volume_hyperplane_eq_zero i

/-- A cutoff `χ` (in `[0,1]`, vanishing where `x i ≤ 1/(m+1)`) times a test function `φ` is a test
function on the open upper half-space. -/
theorem isTestFunction_cutoffPos_mul (i : Fin n) (m : ℕ) {φ : ℝⁿ → ℝ}
    (hφ : IsTestFunction Set.univ φ) :
    IsTestFunction {x : ℝⁿ | 0 < x i} (fun x => cutoffPos i m x * φ x) := by
  refine ⟨(cutoffPos_contDiff i m).mul hφ.contDiff, hφ.hasCompactSupport.mul_left, ?_⟩
  have hcl : IsClosed {x : ℝⁿ | (1 : ℝ) / (m + 1) ≤ x i} :=
    isClosed_le continuous_const (EuclideanSpace.proj i).continuous
  have hsupp : Function.support (fun x => cutoffPos i m x * φ x)
      ⊆ {x : ℝⁿ | (1 : ℝ) / (m + 1) ≤ x i} := by
    intro x hx
    by_contra hlt
    simp only [Set.mem_setOf_eq, not_le] at hlt
    have hle : (m + 1 : ℝ) * x i ≤ 1 := by
      rw [lt_div_iff₀ (by positivity : (0:ℝ) < (m:ℝ) + 1)] at hlt; nlinarith [hlt]
    exact hx (by simp [cutoffPos_eq_zero_of_le i m hle])
  refine (closure_minimal hsupp hcl).trans (fun x hx => ?_)
  simp only [Set.mem_setOf_eq] at hx ⊢
  exact lt_of_lt_of_le (by positivity) hx

/-- Companion of `isTestFunction_cutoffPos_mul` for the lower half-space. -/
theorem isTestFunction_cutoffNeg_mul (i : Fin n) (m : ℕ) {φ : ℝⁿ → ℝ}
    (hφ : IsTestFunction Set.univ φ) :
    IsTestFunction {x : ℝⁿ | x i < 0} (fun x => cutoffNeg i m x * φ x) := by
  refine ⟨(cutoffNeg_contDiff i m).mul hφ.contDiff, hφ.hasCompactSupport.mul_left, ?_⟩
  have hcl : IsClosed {x : ℝⁿ | x i ≤ -(1 : ℝ) / (m + 1)} :=
    isClosed_le (EuclideanSpace.proj i).continuous continuous_const
  have hsupp : Function.support (fun x => cutoffNeg i m x * φ x)
      ⊆ {x : ℝⁿ | x i ≤ -(1 : ℝ) / (m + 1)} := by
    intro x hx
    by_contra hlt
    simp only [Set.mem_setOf_eq, not_le] at hlt
    have hz : cutoffNeg i m x = 0 := by
      apply cutoffPos_eq_zero_of_le i m
      rw [refll_apply_self]
      rw [div_lt_iff₀ (by positivity : (0:ℝ) < (m:ℝ) + 1)] at hlt
      nlinarith [hlt]
    exact hx (by simp [hz])
  refine (closure_minimal hsupp hcl).trans (fun x hx => ?_)
  simp only [Set.mem_setOf_eq] at hx ⊢
  have hneg : -(1 : ℝ) / (m + 1) < 0 := div_neg_of_neg_of_pos (by norm_num) (by positivity)
  exact lt_of_le_of_lt hx hneg

/-- **Tangential gluing of one-sided weak derivatives.** If `w` is continuous, and has weak
`eⱼ`-derivative `gp` on the open upper half `{xᵢ > 0}` and `gm` on the open lower half `{xᵢ < 0}`,
for a **tangential** direction `j ≠ i`, then `w` has a weak `eⱼ`-derivative on all of `ℝⁿ`, equal to
the piecewise glue.  No boundary term appears because the cutoff varies only in the normal (`i`)
direction, so `∂ⱼ` of it vanishes; the two half-space identities are stitched by dominated
convergence, the boundary hyperplane being Lebesgue-null. -/
theorem isWeakDerivInDir_glue_tangential (i j : Fin n) (hji : j ≠ i) {w gp gm : ℝⁿ → ℝ}
    (hwc : Continuous w) (hgp : LocallyIntegrable gp volume) (hgm : LocallyIntegrable gm volume)
    (hp : IsWeakDerivInDir {x : ℝⁿ | 0 < x i} (EuclideanSpace.single j (1 : ℝ)) w gp)
    (hm : IsWeakDerivInDir {x : ℝⁿ | x i < 0} (EuclideanSpace.single j (1 : ℝ)) w gm) :
    IsWeakDerivInDir Set.univ (EuclideanSpace.single j (1 : ℝ)) w
      (fun x => if 0 < x i then gp x else gm x) := by
  intro φ hφ
  set e := EuclideanSpace.single j (1 : ℝ) with he
  -- Product rule (tangential): `∂ₑ(χ·φ) = χ·∂ₑφ` since `∂ₑχ = 0`.
  have hdP : ∀ m x, fderiv ℝ (fun y => cutoffPos i m y * φ y) x e
      = cutoffPos i m x * fderiv ℝ φ x e := by
    intro m x
    have hf := ((cutoffPos_contDiff i m).differentiable (by norm_num) x).hasFDerivAt
    have hg := (hφ.differentiable x).hasFDerivAt
    have hmul : fderiv ℝ (fun y => cutoffPos i m y * φ y) x
        = cutoffPos i m x • fderiv ℝ φ x + φ x • fderiv ℝ (cutoffPos i m) x := (hf.mul hg).fderiv
    rw [hmul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, smul_eq_mul, he,
      cutoffPos_fderiv_tangential i j hji m x]
    ring
  have hdN : ∀ m x, fderiv ℝ (fun y => cutoffNeg i m y * φ y) x e
      = cutoffNeg i m x * fderiv ℝ φ x e := by
    intro m x
    have hf := ((cutoffNeg_contDiff i m).differentiable (by norm_num) x).hasFDerivAt
    have hg := (hφ.differentiable x).hasFDerivAt
    have hmul : fderiv ℝ (fun y => cutoffNeg i m y * φ y) x
        = cutoffNeg i m x • fderiv ℝ φ x + φ x • fderiv ℝ (cutoffNeg i m) x := (hf.mul hg).fderiv
    rw [hmul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, smul_eq_mul, he,
      cutoffNeg_fderiv_tangential i j hji m x]
    ring
  -- The two one-sided integration-by-parts identities, rewritten with the product rule.
  have hP : ∀ m, ∫ x, w x * (cutoffPos i m x * fderiv ℝ φ x e)
      = -∫ x, gp x * (cutoffPos i m x * φ x) := by
    intro m
    have key := hp (fun y => cutoffPos i m y * φ y) (isTestFunction_cutoffPos_mul i m hφ)
    simp only [] at key
    rw [← key]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun x => by simp only [hdP m x]))
  have hN : ∀ m, ∫ x, w x * (cutoffNeg i m x * fderiv ℝ φ x e)
      = -∫ x, gm x * (cutoffNeg i m x * φ x) := by
    intro m
    have key := hm (fun y => cutoffNeg i m y * φ y) (isTestFunction_cutoffNeg_mul i m hφ)
    simp only [] at key
    rw [← key]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun x => by simp only [hdN m x]))
  -- Integrability of the dominating functions.
  have hwd_int : Integrable (fun x => w x * fderiv ℝ φ x e) volume :=
    (hwc.mul (hφ.continuous_dirDeriv e)).integrable_of_hasCompactSupport
      ((hφ.hasCompactSupport_dirDeriv e).mul_left)
  have hgpφ_int : Integrable (fun x => gp x * φ x) volume := integrable_mul_testFunction hgp hφ
  have hgnφ_int : Integrable (fun x => gm x * φ x) volume := integrable_mul_testFunction hgm hφ
  -- Integrability of each cutoff-weighted summand.
  have intP : ∀ m, Integrable (fun x => w x * (cutoffPos i m x * fderiv ℝ φ x e)) volume := by
    intro m
    refine hwd_int.abs.mono'
      (hwc.aestronglyMeasurable.mul ((cutoffPos_contDiff i m).continuous.aestronglyMeasurable.mul
        (hφ.continuous_dirDeriv e).aestronglyMeasurable))
      (Filter.Eventually.of_forall (fun x => ?_))
    rw [Real.norm_eq_abs,
      show w x * (cutoffPos i m x * fderiv ℝ φ x e)
        = cutoffPos i m x * (w x * fderiv ℝ φ x e) by ring,
      abs_mul, abs_of_nonneg (cutoffPos_nonneg i m x)]
    exact mul_le_of_le_one_left (abs_nonneg _) (cutoffPos_le_one i m x)
  have intN : ∀ m, Integrable (fun x => w x * (cutoffNeg i m x * fderiv ℝ φ x e)) volume := by
    intro m
    refine hwd_int.abs.mono'
      (hwc.aestronglyMeasurable.mul ((cutoffNeg_contDiff i m).continuous.aestronglyMeasurable.mul
        (hφ.continuous_dirDeriv e).aestronglyMeasurable))
      (Filter.Eventually.of_forall (fun x => ?_))
    rw [Real.norm_eq_abs,
      show w x * (cutoffNeg i m x * fderiv ℝ φ x e)
        = cutoffNeg i m x * (w x * fderiv ℝ φ x e) by ring,
      abs_mul, abs_of_nonneg (cutoffNeg_nonneg i m x)]
    exact mul_le_of_le_one_left (abs_nonneg _) (cutoffNeg_le_one i m x)
  -- LHS limit: `∫ w χ⁺ ∂ₑφ + ∫ w χ⁻ ∂ₑφ → ∫ w ∂ₑφ` via dominated convergence.
  have hLHS : Tendsto (fun m => (∫ x, w x * (cutoffPos i m x * fderiv ℝ φ x e))
      + ∫ x, w x * (cutoffNeg i m x * fderiv ℝ φ x e)) atTop
      (nhds (∫ x, w x * fderiv ℝ φ x e)) := by
    have hmerge : ∀ m, (∫ x, w x * (cutoffPos i m x * fderiv ℝ φ x e))
        + ∫ x, w x * (cutoffNeg i m x * fderiv ℝ φ x e)
        = ∫ x, (w x * (cutoffPos i m x * fderiv ℝ φ x e)
            + w x * (cutoffNeg i m x * fderiv ℝ φ x e)) := fun m =>
      (integral_add (intP m) (intN m)).symm
    simp_rw [hmerge]
    refine tendsto_integral_of_dominated_convergence (fun x => 2 * |w x * fderiv ℝ φ x e|)
      (fun m => ((intP m).add (intN m)).aestronglyMeasurable) (hwd_int.abs.const_mul 2)
      (fun m => Filter.Eventually.of_forall (fun x => ?_)) ?_
    · rw [show w x * (cutoffPos i m x * fderiv ℝ φ x e) + w x * (cutoffNeg i m x * fderiv ℝ φ x e)
          = (cutoffPos i m x + cutoffNeg i m x) * (w x * fderiv ℝ φ x e) by ring,
        Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (add_nonneg (cutoffPos_nonneg i m x) (cutoffNeg_nonneg i m x))]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      have := cutoffPos_le_one i m x; have := cutoffNeg_le_one i m x; linarith
    · filter_upwards [ae_coord_ne_zero i] with x hx0
      have hs : Tendsto (fun m => cutoffPos i m x + cutoffNeg i m x) atTop (nhds 1) := by
        rcases lt_or_gt_of_ne hx0 with hlt | hgt
        · have h0 : ∀ m, cutoffPos i m x = 0 := fun m => cutoffPos_eq_zero i m hlt.le
          simpa [h0] using cutoffNeg_tendsto_one i hlt
        · have h0 : ∀ m, cutoffNeg i m x = 0 := fun m => cutoffNeg_eq_zero i m hgt.le
          simpa [h0] using cutoffPos_tendsto_one i hgt
      have hlim := (hs.mul_const (fderiv ℝ φ x e)).const_mul (w x)
      rw [one_mul] at hlim
      refine hlim.congr (fun m => by ring)
  -- RHS limits.
  have hmsP : MeasurableSet {x : ℝⁿ | 0 < x i} :=
    measurableSet_lt measurable_const (EuclideanSpace.proj i).continuous.measurable
  have hmsN : MeasurableSet {x : ℝⁿ | x i < 0} :=
    measurableSet_lt (EuclideanSpace.proj i).continuous.measurable measurable_const
  have hBP : Tendsto (fun m => ∫ x, gp x * (cutoffPos i m x * φ x)) atTop
      (nhds (∫ x, if 0 < x i then gp x * φ x else 0)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => |gp x * φ x|)
      (fun m => hgp.aestronglyMeasurable.mul
        ((cutoffPos_contDiff i m).continuous.aestronglyMeasurable.mul
          hφ.continuous.aestronglyMeasurable))
      hgpφ_int.abs (fun m => Filter.Eventually.of_forall (fun x => ?_))
      (Filter.Eventually.of_forall (fun x => ?_))
    · rw [Real.norm_eq_abs,
        show gp x * (cutoffPos i m x * φ x) = cutoffPos i m x * (gp x * φ x) by ring,
        abs_mul, abs_of_nonneg (cutoffPos_nonneg i m x)]
      exact mul_le_of_le_one_left (abs_nonneg _) (cutoffPos_le_one i m x)
    · by_cases hgt : 0 < x i
      · rw [if_pos hgt]
        have hlim := ((cutoffPos_tendsto_one i hgt).mul_const (φ x)).const_mul (gp x)
        rw [one_mul] at hlim
        exact hlim
      · have h0 : ∀ m, cutoffPos i m x = 0 := fun m => cutoffPos_eq_zero i m (not_lt.1 hgt)
        simp only [h0, mul_zero, zero_mul, if_neg hgt]
        exact tendsto_const_nhds
  have hBN : Tendsto (fun m => ∫ x, gm x * (cutoffNeg i m x * φ x)) atTop
      (nhds (∫ x, if x i < 0 then gm x * φ x else 0)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => |gm x * φ x|)
      (fun m => hgm.aestronglyMeasurable.mul
        ((cutoffNeg_contDiff i m).continuous.aestronglyMeasurable.mul
          hφ.continuous.aestronglyMeasurable))
      hgnφ_int.abs (fun m => Filter.Eventually.of_forall (fun x => ?_))
      (Filter.Eventually.of_forall (fun x => ?_))
    · rw [Real.norm_eq_abs,
        show gm x * (cutoffNeg i m x * φ x) = cutoffNeg i m x * (gm x * φ x) by ring,
        abs_mul, abs_of_nonneg (cutoffNeg_nonneg i m x)]
      exact mul_le_of_le_one_left (abs_nonneg _) (cutoffNeg_le_one i m x)
    · by_cases hlt : x i < 0
      · rw [if_pos hlt]
        have hlim := ((cutoffNeg_tendsto_one i hlt).mul_const (φ x)).const_mul (gm x)
        rw [one_mul] at hlim
        exact hlim
      · have h0 : ∀ m, cutoffNeg i m x = 0 := fun m => cutoffNeg_eq_zero i m (not_lt.1 hlt)
        simp only [h0, mul_zero, zero_mul, if_neg hlt]
        exact tendsto_const_nhds
  -- Assemble: `AP+AN = -(BP+BN)`, take limits, use uniqueness, then combine the two RHS integrals.
  have hAeqB : ∀ m, (∫ x, w x * (cutoffPos i m x * fderiv ℝ φ x e))
      + ∫ x, w x * (cutoffNeg i m x * fderiv ℝ φ x e)
      = -((∫ x, gp x * (cutoffPos i m x * φ x)) + ∫ x, gm x * (cutoffNeg i m x * φ x)) := by
    intro m; rw [hP m, hN m]; ring
  have hL2 : Tendsto (fun m => -((∫ x, gp x * (cutoffPos i m x * φ x))
      + ∫ x, gm x * (cutoffNeg i m x * φ x))) atTop (nhds (∫ x, w x * fderiv ℝ φ x e)) := by
    simp_rw [← hAeqB]; exact hLHS
  have hunique := tendsto_nhds_unique hL2 (hBP.add hBN).neg
  -- Combine the two half-space integrals into the piecewise glue (boundary is null).
  have hBPlim_int : Integrable (fun x => if 0 < x i then gp x * φ x else 0) volume := by
    refine (hgpφ_int.indicator hmsP).congr (Filter.Eventually.of_forall (fun x => ?_))
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
  have hBNlim_int : Integrable (fun x => if x i < 0 then gm x * φ x else 0) volume := by
    refine (hgnφ_int.indicator hmsN).congr (Filter.Eventually.of_forall (fun x => ?_))
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
  have hcomb : (∫ x, (if 0 < x i then gp x * φ x else 0))
      + (∫ x, (if x i < 0 then gm x * φ x else 0))
      = ∫ x, (if 0 < x i then gp x else gm x) * φ x := by
    rw [← integral_add hBPlim_int hBNlim_int]
    refine integral_congr_ae ((ae_coord_ne_zero i).mono (fun x hx0 => ?_))
    dsimp only
    rcases lt_or_gt_of_ne hx0 with hlt | hgt
    · rw [if_neg (not_lt.2 hlt.le), if_pos hlt, if_neg (not_lt.2 hlt.le), zero_add]
    · rw [if_pos hgt, if_neg (not_lt.2 hgt.le), if_pos hgt, add_zero]
  rw [hunique, ← hcomb]



theorem deriv_smoothTransition_eq_zero_of_neg {s : ℝ} (hs : s < 0) :
    deriv Real.smoothTransition s = 0 := by
  have h : Real.smoothTransition =ᶠ[nhds s] (fun _ => 0) := by
    filter_upwards [Iio_mem_nhds hs] with t ht using Real.smoothTransition.zero_of_nonpos ht.le
  rw [h.deriv_eq]; simp

theorem deriv_smoothTransition_eq_zero_of_gt_one {s : ℝ} (hs : 1 < s) :
    deriv Real.smoothTransition s = 0 := by
  have h : Real.smoothTransition =ᶠ[nhds s] (fun _ => 1) := by
    filter_upwards [Ioi_mem_nhds hs] with t ht using Real.smoothTransition.one_of_one_le ht.le
  rw [h.deriv_eq]; simp

/-- `|s+1|·|sT'(s)|` is bounded: `sT'` is continuous with support in `[0,1]`. -/
theorem exists_smoothTransition_deriv_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s, |s + 1| * |deriv Real.smoothTransition s| ≤ B := by
  have hcont : Continuous (fun s => (s + 1) * deriv Real.smoothTransition s) :=
    (continuous_id.add continuous_const).mul
      ((Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).continuous_deriv (by norm_num))
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun s => ?_⟩
  by_cases hs : s ∈ Set.Icc (0 : ℝ) 1
  · calc |s + 1| * |deriv Real.smoothTransition s|
        = ‖(s + 1) * deriv Real.smoothTransition s‖ := by rw [Real.norm_eq_abs, abs_mul]
      _ ≤ C := hC s hs
      _ ≤ max C 0 := le_max_left _ _
  · rw [Set.mem_Icc, not_and_or, not_le, not_le] at hs
    rcases hs with h | h
    · rw [deriv_smoothTransition_eq_zero_of_neg h, abs_zero, mul_zero]; exact le_max_right _ _
    · rw [deriv_smoothTransition_eq_zero_of_gt_one h, abs_zero, mul_zero]; exact le_max_right _ _

/-- Closed form of the **normal** directional derivative of `cutoffPos`. -/
theorem cutoffPos_fderiv_normal (i : Fin n) (m : ℕ) (x : ℝⁿ) :
    fderiv ℝ (cutoffPos i m) x (EuclideanSpace.single i (1 : ℝ))
      = (m + 1 : ℝ) * deriv Real.smoothTransition ((m + 1 : ℝ) * x i - 1) := by
  have hg' : HasFDerivAt (fun y : ℝⁿ => (m + 1 : ℝ) * y i - 1)
      ((m + 1 : ℝ) • (EuclideanSpace.proj i : ℝⁿ →L[ℝ] ℝ)) x :=
    (((EuclideanSpace.proj i : ℝⁿ →L[ℝ] ℝ).hasFDerivAt).const_mul (m + 1 : ℝ)).sub_const 1
  have hst : HasDerivAt Real.smoothTransition
      (deriv Real.smoothTransition ((m + 1 : ℝ) * x i - 1)) ((m + 1 : ℝ) * x i - 1) :=
    ((Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).differentiable
      (by norm_num)).differentiableAt.hasDerivAt
  have hcomp : HasFDerivAt (cutoffPos i m)
      (deriv Real.smoothTransition ((m + 1 : ℝ) * x i - 1)
        • ((m + 1 : ℝ) • (EuclideanSpace.proj i : ℝⁿ →L[ℝ] ℝ))) x :=
    hst.comp_hasFDerivAt x hg'
  have hpe : ((m + 1 : ℝ) • (EuclideanSpace.proj i : ℝⁿ →L[ℝ] ℝ))
      (EuclideanSpace.single i (1 : ℝ)) = (m + 1 : ℝ) := by
    rw [ContinuousLinearMap.smul_apply]
    change (m + 1 : ℝ) • ((EuclideanSpace.single i (1 : ℝ)) i) = (m + 1 : ℝ)
    rw [PiLp.single_apply, if_pos rfl, smul_eq_mul, mul_one]
  rw [hcomp.fderiv, ContinuousLinearMap.smul_apply, hpe, smul_eq_mul]; ring

/-- Reflection symmetry of the **normal** cutoff derivative: `∂ᵢχ⁻ = -(∂ᵢχ⁺)∘refll`. -/
theorem cutoffNeg_fderiv_normal (i : Fin n) (m : ℕ) (x : ℝⁿ) :
    fderiv ℝ (cutoffNeg i m) x (EuclideanSpace.single i (1 : ℝ))
      = - fderiv ℝ (cutoffPos i m) (refll i x) (EuclideanSpace.single i (1 : ℝ)) := by
  have hcomp : HasFDerivAt (cutoffNeg i m)
      ((fderiv ℝ (cutoffPos i m) (refll i x)).comp
        ((refll i).toContinuousLinearEquiv : ℝⁿ →L[ℝ] ℝⁿ)) x :=
    ((cutoffPos_contDiff i m).differentiable (by norm_num) (refll i x)).hasFDerivAt.comp x
      (refll i).toContinuousLinearEquiv.hasFDerivAt
  rw [hcomp.fderiv, ContinuousLinearMap.comp_apply]
  change fderiv ℝ (cutoffPos i m) (refll i x) (refll i (EuclideanSpace.single i (1 : ℝ))) = _
  rw [refll_single, if_pos rfl, neg_one_smul, map_neg]

/-- Continuity of the normal cutoff derivative (as a function of the base point). -/
theorem continuous_cutoffPos_fderiv_normal (i : Fin n) (m : ℕ) :
    Continuous (fun x => fderiv ℝ (cutoffPos i m) x (EuclideanSpace.single i (1 : ℝ))) :=
  ((cutoffPos_contDiff i m).continuous_fderiv (by norm_num)).clm_apply continuous_const

/-- **Reflection-symmetry reformulation of the boundary term.** Combining `∂ᵢχ⁺` and `∂ᵢχ⁻` via the
reflection symmetry and the measure-preserving substitution `x = refll i y` collapses the boundary
term into a single integral against `∂ᵢχ⁺` of the reflection-difference `F - F∘refll`. -/
theorem boundary_reformulation (i : Fin n) (m : ℕ) {F : ℝⁿ → ℝ}
    (hFc : Continuous F) (hFs : HasCompactSupport F) :
    ∫ x, F x * (fderiv ℝ (cutoffPos i m) x (EuclideanSpace.single i (1 : ℝ))
        + fderiv ℝ (cutoffNeg i m) x (EuclideanSpace.single i (1 : ℝ)))
      = ∫ x, (F x - F (refll i x))
          * fderiv ℝ (cutoffPos i m) x (EuclideanSpace.single i (1 : ℝ)) := by
  have hdc : Continuous (fun x => fderiv ℝ (cutoffPos i m) x (EuclideanSpace.single i (1 : ℝ))) :=
    continuous_cutoffPos_fderiv_normal i m
  have hdcN : Continuous
      (fun x => fderiv ℝ (cutoffNeg i m) x (EuclideanSpace.single i (1 : ℝ))) := by
    simp only [cutoffNeg_fderiv_normal]
    exact (hdc.comp (contDiff_refll i).continuous).neg
  have hint1 : Integrable (fun x => F x
      * fderiv ℝ (cutoffPos i m) x (EuclideanSpace.single i (1 : ℝ))) volume :=
    (hFc.mul hdc).integrable_of_hasCompactSupport hFs.mul_right
  have hint2 : Integrable (fun x => F x
      * fderiv ℝ (cutoffNeg i m) x (EuclideanSpace.single i (1 : ℝ))) volume :=
    (hFc.mul hdcN).integrable_of_hasCompactSupport hFs.mul_right
  have hintR : Integrable (fun x => F (refll i x)
      * fderiv ℝ (cutoffPos i m) x (EuclideanSpace.single i (1 : ℝ))) volume :=
    ((hFc.comp (contDiff_refll i).continuous).mul hdc).integrable_of_hasCompactSupport
      ((hFs.comp_homeomorph (refll i).toHomeomorph).mul_right)
  have hsub : ∫ x, F x * fderiv ℝ (cutoffPos i m) (refll i x) (EuclideanSpace.single i (1 : ℝ))
      = ∫ x, F (refll i x) * fderiv ℝ (cutoffPos i m) x (EuclideanSpace.single i (1 : ℝ)) := by
    have key := (refll_measurePreserving i).integral_comp (refll_measurableEmbedding i)
      (fun y => F (refll i y) * fderiv ℝ (cutoffPos i m) y (EuclideanSpace.single i (1 : ℝ)))
    have hinv : ∀ y, refll i (refll i y) = y := refll_involutive i
    simp only [hinv] at key
    exact key
  have e1 : ∫ x, F x * (fderiv ℝ (cutoffPos i m) x (EuclideanSpace.single i (1 : ℝ))
        + fderiv ℝ (cutoffNeg i m) x (EuclideanSpace.single i (1 : ℝ)))
      = (∫ x, F x * fderiv ℝ (cutoffPos i m) x (EuclideanSpace.single i (1 : ℝ)))
        + ∫ x, F x * fderiv ℝ (cutoffNeg i m) x (EuclideanSpace.single i (1 : ℝ)) := by
    rw [← integral_add hint1 hint2]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun x => by ring))
  have e2 : ∫ x, F x * fderiv ℝ (cutoffNeg i m) x (EuclideanSpace.single i (1 : ℝ))
      = -∫ x, F (refll i x) * fderiv ℝ (cutoffPos i m) x (EuclideanSpace.single i (1 : ℝ)) := by
    rw [← hsub, ← integral_neg]
    exact integral_congr_ae (Filter.Eventually.of_forall
      (fun x => by simp only [cutoffNeg_fderiv_normal]; ring))
  rw [e1, e2, ← sub_eq_add_neg, ← integral_sub hint1 hintR]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun x => by ring))

/-- **The normal boundary term vanishes in the limit.** For `F` continuous with compact support and
Lipschitz-in-`xᵢ` difference bound `|F x - F(refll x)| ≤ L·|xᵢ|`, the boundary-layer integral
`∫ (F - F∘refll)·∂ᵢχ⁺_m → 0`.  The `(m+1)` blow-up of `∂ᵢχ⁺_m` is compensated by the
`|xᵢ| ≲ 1/(m+1)` smallness of `F - F∘refll` on the cutoff's support, so a single `m`-independent
dominating function `(L·B)·1_K` works and dominated convergence applies directly (no CoV). -/
theorem boundary_tendsto_zero (i : Fin n) {F : ℝⁿ → ℝ}
    (hFc : Continuous F) (hFs : HasCompactSupport F)
    {L : ℝ} (hL0 : 0 ≤ L) (hL : ∀ x, |F x - F (refll i x)| ≤ L * |x i|) :
    Tendsto (fun m => ∫ x, (F x - F (refll i x))
        * fderiv ℝ (cutoffPos i m) x (EuclideanSpace.single i (1 : ℝ))) atTop (nhds 0) := by
  obtain ⟨B, hB0, hB⟩ := exists_smoothTransition_deriv_bound
  have hcs : HasCompactSupport (fun x => F x - F (refll i x)) :=
    hFs.sub (hFs.comp_homeomorph (refll i).toHomeomorph)
  set K := tsupport (fun x => F x - F (refll i x)) with hKdef
  have hKc : IsCompact K := hcs
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  have hdiffc : Continuous (fun x => F x - F (refll i x)) :=
    hFc.sub (hFc.comp (contDiff_refll i).continuous)
  have key : Tendsto (fun m => ∫ x, (F x - F (refll i x))
      * fderiv ℝ (cutoffPos i m) x (EuclideanSpace.single i (1 : ℝ))) atTop
      (nhds (∫ (_ : ℝⁿ), (0 : ℝ))) := by
    refine tendsto_integral_of_dominated_convergence (K.indicator (fun _ => L * B))
      (fun m => (hdiffc.mul (continuous_cutoffPos_fderiv_normal i m)).aestronglyMeasurable)
      ((integrable_indicator_iff hKm).2 (integrableOn_const hKc.measure_lt_top.ne))
      (fun m => Filter.Eventually.of_forall (fun x => ?_)) ?_
    · by_cases hxK : x ∈ K
      · rw [Set.indicator_of_mem hxK, cutoffPos_fderiv_normal, Real.norm_eq_abs, abs_mul,
          abs_mul, abs_of_pos (show (0 : ℝ) < (m : ℝ) + 1 by positivity)]
        calc |F x - F (refll i x)| * ((m + 1 : ℝ)
              * |deriv Real.smoothTransition ((m + 1 : ℝ) * x i - 1)|)
            ≤ (L * |x i|) * ((m + 1 : ℝ)
              * |deriv Real.smoothTransition ((m + 1 : ℝ) * x i - 1)|) := by
              gcongr; exact hL x
          _ = L * (|(m + 1 : ℝ) * x i|
              * |deriv Real.smoothTransition ((m + 1 : ℝ) * x i - 1)|) := by
              rw [abs_mul, abs_of_pos (show (0 : ℝ) < (m : ℝ) + 1 by positivity)]; ring
          _ ≤ L * B := by
              refine mul_le_mul_of_nonneg_left ?_ hL0
              have hb := hB ((m + 1 : ℝ) * x i - 1)
              have he : (m + 1 : ℝ) * x i - 1 + 1 = (m + 1 : ℝ) * x i := by ring
              rwa [he] at hb
      · rw [Set.indicator_of_notMem hxK,
          show F x - F (refll i x) = 0 from by_contra fun hne => hxK (subset_tsupport _ hne),
          zero_mul, norm_zero]
    · filter_upwards [ae_coord_ne_zero i] with x hx0
      apply tendsto_const_nhds.congr'
      rw [Filter.EventuallyEq, eventually_atTop]
      have hz : ∀ᶠ m : ℕ in atTop,
          deriv Real.smoothTransition (((m : ℝ) + 1) * x i - 1) = 0 := by
        rcases lt_or_gt_of_ne hx0 with hlt | hgt
        · refine Filter.Eventually.of_forall (fun m => deriv_smoothTransition_eq_zero_of_neg ?_)
          have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
          nlinarith [hm0, hlt]
        · rw [eventually_atTop]
          obtain ⟨M, hM⟩ := exists_nat_ge (2 / x i)
          refine ⟨M, fun m hm => deriv_smoothTransition_eq_zero_of_gt_one ?_⟩
          have hmM : (2 / x i) ≤ (m : ℝ) := hM.trans (by exact_mod_cast hm)
          have hlt2 : (2 : ℝ) < ((m : ℝ) + 1) * x i := by
            have := (div_le_iff₀ hgt).1 hmM; nlinarith [this]
          linarith
      obtain ⟨M, hM⟩ := eventually_atTop.1 hz
      refine ⟨M, fun m hm => ?_⟩
      simp only [cutoffPos_fderiv_normal, hM m hm, mul_zero]
  simpa using key



/-- **Normal gluing of one-sided weak derivatives.** If `w` is continuous with the reflection-
Lipschitz bound `|w·φ − (w·φ)∘refll| ≤ L·|xᵢ|` on every test function `φ`, and has weak
`eᵢ`-derivative `gp` on `{xᵢ > 0}` and `gm` on `{xᵢ < 0}` in the **normal** direction, then `w` has
weak `eᵢ`-derivative on all of `ℝⁿ`, the piecewise glue. The boundary term from `∂ᵢ` of the cutoff
tends to `0` (`boundary_reformulation` + `boundary_tendsto_zero`); the rest mirrors the tangential
glue. -/
theorem isWeakDerivInDir_glue_normal (i : Fin n) {w gp gm : ℝⁿ → ℝ}
    (hwc : Continuous w) (hgp : LocallyIntegrable gp volume) (hgm : LocallyIntegrable gm volume)
    (hp : IsWeakDerivInDir {x : ℝⁿ | 0 < x i} (EuclideanSpace.single i (1 : ℝ)) w gp)
    (hm : IsWeakDerivInDir {x : ℝⁿ | x i < 0} (EuclideanSpace.single i (1 : ℝ)) w gm)
    (hLip : ∀ φ : ℝⁿ → ℝ, IsTestFunction Set.univ φ →
      ∃ L : ℝ, 0 ≤ L ∧ ∀ x, |w x * φ x - w (refll i x) * φ (refll i x)| ≤ L * |x i|) :
    IsWeakDerivInDir Set.univ (EuclideanSpace.single i (1 : ℝ)) w
      (fun x => if 0 < x i then gp x else gm x) := by
  intro φ hφ
  -- Product rule (normal): keep the `∂ᵢχ` term.
  have hdP : ∀ m x, fderiv ℝ (fun y => cutoffPos i m y * φ y) x (EuclideanSpace.single i (1 : ℝ))
      = fderiv ℝ (cutoffPos i m) x (EuclideanSpace.single i (1 : ℝ)) * φ x
        + cutoffPos i m x * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)) := by
    intro m x
    have hf := ((cutoffPos_contDiff i m).differentiable (by norm_num) x).hasFDerivAt
    have hg := (hφ.differentiable x).hasFDerivAt
    have hmul : fderiv ℝ (fun y => cutoffPos i m y * φ y) x
        = cutoffPos i m x • fderiv ℝ φ x + φ x • fderiv ℝ (cutoffPos i m) x := (hf.mul hg).fderiv
    rw [hmul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, smul_eq_mul]; ring
  have hdN : ∀ m x, fderiv ℝ (fun y => cutoffNeg i m y * φ y) x (EuclideanSpace.single i (1 : ℝ))
      = fderiv ℝ (cutoffNeg i m) x (EuclideanSpace.single i (1 : ℝ)) * φ x
        + cutoffNeg i m x * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)) := by
    intro m x
    have hf := ((cutoffNeg_contDiff i m).differentiable (by norm_num) x).hasFDerivAt
    have hg := (hφ.differentiable x).hasFDerivAt
    have hmul : fderiv ℝ (fun y => cutoffNeg i m y * φ y) x
        = cutoffNeg i m x • fderiv ℝ φ x + φ x • fderiv ℝ (cutoffNeg i m) x := (hf.mul hg).fderiv
    rw [hmul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, smul_eq_mul]; ring
  -- Continuity / integrability helpers.
  have hdcP : ∀ m, Continuous
      (fun x => fderiv ℝ (cutoffPos i m) x (EuclideanSpace.single i (1 : ℝ))) :=
    fun m => continuous_cutoffPos_fderiv_normal i m
  have hdcN : ∀ m, Continuous
      (fun x => fderiv ℝ (cutoffNeg i m) x (EuclideanSpace.single i (1 : ℝ))) := fun m => by
    simp only [cutoffNeg_fderiv_normal]; exact (hdcP m).comp (contDiff_refll i).continuous |>.neg
  have hSPint : ∀ m, Integrable (fun x => w x
      * (cutoffPos i m x * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)))) volume := fun m =>
    (hwc.mul ((cutoffPos_contDiff i m).continuous.mul
      (hφ.continuous_dirDeriv _))).integrable_of_hasCompactSupport
      ((hφ.hasCompactSupport_dirDeriv _).mul_left.mul_left)
  have hSNint : ∀ m, Integrable (fun x => w x
      * (cutoffNeg i m x * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)))) volume := fun m =>
    (hwc.mul ((cutoffNeg_contDiff i m).continuous.mul
      (hφ.continuous_dirDeriv _))).integrable_of_hasCompactSupport
      ((hφ.hasCompactSupport_dirDeriv _).mul_left.mul_left)
  have hBPint : ∀ m, Integrable (fun x => w x
      * (fderiv ℝ (cutoffPos i m) x (EuclideanSpace.single i (1 : ℝ)) * φ x)) volume := fun m =>
    (hwc.mul ((hdcP m).mul hφ.continuous)).integrable_of_hasCompactSupport
      (hφ.hasCompactSupport.mul_left.mul_left)
  have hBNint : ∀ m, Integrable (fun x => w x
      * (fderiv ℝ (cutoffNeg i m) x (EuclideanSpace.single i (1 : ℝ)) * φ x)) volume := fun m =>
    (hwc.mul ((hdcN m).mul hφ.continuous)).integrable_of_hasCompactSupport
      (hφ.hasCompactSupport.mul_left.mul_left)
  -- One-sided integration-by-parts, split into boundary + tangential parts.
  have hP : ∀ m, (∫ x, w x * (fderiv ℝ (cutoffPos i m) x (EuclideanSpace.single i (1 : ℝ)) * φ x))
      + ∫ x, w x * (cutoffPos i m x * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)))
      = -∫ x, gp x * (cutoffPos i m x * φ x) := by
    intro m
    have key := hp (fun y => cutoffPos i m y * φ y) (isTestFunction_cutoffPos_mul i m hφ)
    simp only [] at key
    rw [← key, ← integral_add (hBPint m) (hSPint m)]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun x => by simp only [hdP m x]; ring))
  have hN : ∀ m, (∫ x, w x * (fderiv ℝ (cutoffNeg i m) x (EuclideanSpace.single i (1 : ℝ)) * φ x))
      + ∫ x, w x * (cutoffNeg i m x * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)))
      = -∫ x, gm x * (cutoffNeg i m x * φ x) := by
    intro m
    have key := hm (fun y => cutoffNeg i m y * φ y) (isTestFunction_cutoffNeg_mul i m hφ)
    simp only [] at key
    rw [← key, ← integral_add (hBNint m) (hSNint m)]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun x => by simp only [hdN m x]; ring))
  -- The boundary term tends to `0`.
  have hFc : Continuous (fun x => w x * φ x) := hwc.mul hφ.continuous
  have hFcs : HasCompactSupport (fun x => w x * φ x) := hφ.hasCompactSupport.mul_left
  obtain ⟨L, hL0, hLb⟩ := hLip φ hφ
  have hbdry : Tendsto (fun m =>
      (∫ x, w x * (fderiv ℝ (cutoffPos i m) x (EuclideanSpace.single i (1 : ℝ)) * φ x))
      + ∫ x, w x * (fderiv ℝ (cutoffNeg i m) x (EuclideanSpace.single i (1 : ℝ)) * φ x)) atTop
      (nhds 0) := by
    have hrefl : ∀ m,
        (∫ x, w x * (fderiv ℝ (cutoffPos i m) x (EuclideanSpace.single i (1 : ℝ)) * φ x))
        + ∫ x, w x * (fderiv ℝ (cutoffNeg i m) x (EuclideanSpace.single i (1 : ℝ)) * φ x)
        = ∫ x, (w x * φ x - w (refll i x) * φ (refll i x))
            * fderiv ℝ (cutoffPos i m) x (EuclideanSpace.single i (1 : ℝ)) := by
      intro m
      rw [← boundary_reformulation i m hFc hFcs, ← integral_add (hBPint m) (hBNint m)]
      exact integral_congr_ae (Filter.Eventually.of_forall (fun x => by ring))
    simp_rw [hrefl]
    exact boundary_tendsto_zero i hFc hFcs hL0 hLb
  -- The tangential part limit (identical to the tangential glue), and the RHS limits.
  have hwd_int :
      Integrable (fun x => w x * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))) volume :=
    (hwc.mul (hφ.continuous_dirDeriv _)).integrable_of_hasCompactSupport
      ((hφ.hasCompactSupport_dirDeriv _).mul_left)
  have hLHS : Tendsto (fun m =>
      (∫ x, w x * (cutoffPos i m x * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))))
      + ∫ x, w x * (cutoffNeg i m x * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)))) atTop
      (nhds (∫ x, w x * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)))) := by
    have hmerge : ∀ m,
        (∫ x, w x * (cutoffPos i m x * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))))
        + ∫ x, w x * (cutoffNeg i m x * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)))
        = ∫ x, (w x * (cutoffPos i m x * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)))
            + w x * (cutoffNeg i m x * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)))) := fun m =>
      (integral_add (hSPint m) (hSNint m)).symm
    simp_rw [hmerge]
    refine tendsto_integral_of_dominated_convergence
      (fun x => 2 * |w x * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))|)
      (fun m => ((hSPint m).add (hSNint m)).aestronglyMeasurable) (hwd_int.abs.const_mul 2)
      (fun m => Filter.Eventually.of_forall (fun x => ?_)) ?_
    · rw [show w x * (cutoffPos i m x * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)))
            + w x * (cutoffNeg i m x * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)))
          = (cutoffPos i m x + cutoffNeg i m x)
            * (w x * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))) by ring,
        Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (add_nonneg (cutoffPos_nonneg i m x) (cutoffNeg_nonneg i m x))]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      have := cutoffPos_le_one i m x; have := cutoffNeg_le_one i m x; linarith
    · filter_upwards [ae_coord_ne_zero i] with x hx0
      have hs : Tendsto (fun m => cutoffPos i m x + cutoffNeg i m x) atTop (nhds 1) := by
        rcases lt_or_gt_of_ne hx0 with hlt | hgt
        · have h0 : ∀ m, cutoffPos i m x = 0 := fun m => cutoffPos_eq_zero i m hlt.le
          simpa [h0] using cutoffNeg_tendsto_one i hlt
        · have h0 : ∀ m, cutoffNeg i m x = 0 := fun m => cutoffNeg_eq_zero i m hgt.le
          simpa [h0] using cutoffPos_tendsto_one i hgt
      have hlim := (hs.mul_const (fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)))).const_mul (w x)
      rw [one_mul] at hlim
      exact hlim.congr (fun m => by ring)
  have hmsP : MeasurableSet {x : ℝⁿ | 0 < x i} :=
    measurableSet_lt measurable_const (EuclideanSpace.proj i).continuous.measurable
  have hmsN : MeasurableSet {x : ℝⁿ | x i < 0} :=
    measurableSet_lt (EuclideanSpace.proj i).continuous.measurable measurable_const
  have hgpφ_int : Integrable (fun x => gp x * φ x) volume := integrable_mul_testFunction hgp hφ
  have hgnφ_int : Integrable (fun x => gm x * φ x) volume := integrable_mul_testFunction hgm hφ
  have hBP : Tendsto (fun m => ∫ x, gp x * (cutoffPos i m x * φ x)) atTop
      (nhds (∫ x, if 0 < x i then gp x * φ x else 0)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => |gp x * φ x|)
      (fun m => hgp.aestronglyMeasurable.mul
        ((cutoffPos_contDiff i m).continuous.aestronglyMeasurable.mul
          hφ.continuous.aestronglyMeasurable))
      hgpφ_int.abs (fun m => Filter.Eventually.of_forall (fun x => ?_))
      (Filter.Eventually.of_forall (fun x => ?_))
    · rw [Real.norm_eq_abs,
        show gp x * (cutoffPos i m x * φ x) = cutoffPos i m x * (gp x * φ x) by ring,
        abs_mul, abs_of_nonneg (cutoffPos_nonneg i m x)]
      exact mul_le_of_le_one_left (abs_nonneg _) (cutoffPos_le_one i m x)
    · by_cases hgt : 0 < x i
      · rw [if_pos hgt]
        have hlim := ((cutoffPos_tendsto_one i hgt).mul_const (φ x)).const_mul (gp x)
        rw [one_mul] at hlim; exact hlim
      · have h0 : ∀ m, cutoffPos i m x = 0 := fun m => cutoffPos_eq_zero i m (not_lt.1 hgt)
        simp only [h0, mul_zero, zero_mul, if_neg hgt]; exact tendsto_const_nhds
  have hBN : Tendsto (fun m => ∫ x, gm x * (cutoffNeg i m x * φ x)) atTop
      (nhds (∫ x, if x i < 0 then gm x * φ x else 0)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => |gm x * φ x|)
      (fun m => hgm.aestronglyMeasurable.mul
        ((cutoffNeg_contDiff i m).continuous.aestronglyMeasurable.mul
          hφ.continuous.aestronglyMeasurable))
      hgnφ_int.abs (fun m => Filter.Eventually.of_forall (fun x => ?_))
      (Filter.Eventually.of_forall (fun x => ?_))
    · rw [Real.norm_eq_abs,
        show gm x * (cutoffNeg i m x * φ x) = cutoffNeg i m x * (gm x * φ x) by ring,
        abs_mul, abs_of_nonneg (cutoffNeg_nonneg i m x)]
      exact mul_le_of_le_one_left (abs_nonneg _) (cutoffNeg_le_one i m x)
    · by_cases hlt : x i < 0
      · rw [if_pos hlt]
        have hlim := ((cutoffNeg_tendsto_one i hlt).mul_const (φ x)).const_mul (gm x)
        rw [one_mul] at hlim; exact hlim
      · have h0 : ∀ m, cutoffNeg i m x = 0 := fun m => cutoffNeg_eq_zero i m (not_lt.1 hlt)
        simp only [h0, mul_zero, zero_mul, if_neg hlt]; exact tendsto_const_nhds
  -- Assemble: `(boundary) + (tangential) = -(RHS)`; take limits and use uniqueness.
  have hAeqB : ∀ m,
      ((∫ x, w x * (fderiv ℝ (cutoffPos i m) x (EuclideanSpace.single i (1 : ℝ)) * φ x))
        + ∫ x, w x * (fderiv ℝ (cutoffNeg i m) x (EuclideanSpace.single i (1 : ℝ)) * φ x))
      + ((∫ x, w x * (cutoffPos i m x * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))))
        + ∫ x, w x * (cutoffNeg i m x * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))))
      = -((∫ x, gp x * (cutoffPos i m x * φ x)) + ∫ x, gm x * (cutoffNeg i m x * φ x)) := by
    intro m
    have ep := hP m; have en := hN m
    linarith [ep, en]
  have hsum_lim : Tendsto (fun m =>
      -((∫ x, gp x * (cutoffPos i m x * φ x)) + ∫ x, gm x * (cutoffNeg i m x * φ x))) atTop
      (nhds (0 + ∫ x, w x * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)))) := by
    simp_rw [← hAeqB]
    exact hbdry.add hLHS
  rw [zero_add] at hsum_lim
  have hunique := tendsto_nhds_unique hsum_lim (hBP.add hBN).neg
  have hBPlim_int : Integrable (fun x => if 0 < x i then gp x * φ x else 0) volume := by
    refine (hgpφ_int.indicator hmsP).congr (Filter.Eventually.of_forall (fun x => ?_))
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
  have hBNlim_int : Integrable (fun x => if x i < 0 then gm x * φ x else 0) volume := by
    refine (hgnφ_int.indicator hmsN).congr (Filter.Eventually.of_forall (fun x => ?_))
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
  have hcomb : (∫ x, (if 0 < x i then gp x * φ x else 0))
      + (∫ x, (if x i < 0 then gm x * φ x else 0))
      = ∫ x, (if 0 < x i then gp x else gm x) * φ x := by
    rw [← integral_add hBPlim_int hBNlim_int]
    refine integral_congr_ae ((ae_coord_ne_zero i).mono (fun x hx0 => ?_))
    dsimp only
    rcases lt_or_gt_of_ne hx0 with hlt | hgt
    · rw [if_neg (not_lt.2 hlt.le), if_pos hlt, if_neg (not_lt.2 hlt.le), zero_add]
    · rw [if_pos hgt, if_neg (not_lt.2 hgt.le), if_pos hgt, add_zero]
  rw [hunique, ← hcomb]



/-- The reflection fixes points on the boundary hyperplane. -/
theorem refll_fixes (i : Fin n) {x : ℝⁿ} (hx : x i = 0) : refll i x = x := by
  ext k
  rcases eq_or_ne k i with rfl | hk
  · simp [hx]
  · rw [refll_apply]; exact reflLin_apply_of_ne i x hk

/-- The **even reflection** of `u` across `{xᵢ = 0}`: `u` on the upper half, `u ∘ refll` below. -/
noncomputable def evenRefl (i : Fin n) (u : ℝⁿ → ℝ) (x : ℝⁿ) : ℝ :=
  if 0 ≤ x i then u x else u (refll i x)

theorem evenRefl_apply_upper (i : Fin n) (u : ℝⁿ → ℝ) {x : ℝⁿ} (hx : 0 ≤ x i) :
    evenRefl i u x = u x := if_pos hx

theorem evenRefl_apply_lower (i : Fin n) (u : ℝⁿ → ℝ) {x : ℝⁿ} (hx : x i < 0) :
    evenRefl i u x = u (refll i x) := if_neg (not_le.2 hx)

/-- The even reflection is invariant under the reflection (it is even). -/
theorem evenRefl_even (i : Fin n) (u : ℝⁿ → ℝ) (x : ℝⁿ) :
    evenRefl i u (refll i x) = evenRefl i u x := by
  rcases lt_trichotomy (x i) 0 with h | h | h
  · rw [evenRefl_apply_upper i u (show 0 ≤ (refll i x) i by rw [refll_apply_self]; linarith),
      evenRefl_apply_lower i u h]
  · rw [refll_fixes i h]
  · rw [evenRefl_apply_lower i u (show (refll i x) i < 0 by rw [refll_apply_self]; linarith),
      evenRefl_apply_upper i u h.le, show refll i (refll i x) = x from refll_involutive i x]

/-- The even reflection of a continuous function is continuous. -/
theorem continuous_evenRefl (i : Fin n) {u : ℝⁿ → ℝ} (hu : Continuous u) :
    Continuous (evenRefl i u) :=
  Continuous.if_le hu (hu.comp (contDiff_refll i).continuous) continuous_const
    (EuclideanSpace.proj i).continuous
    (fun x hx => by rw [refll_fixes i hx.symm])



theorem norm_sub_refll (i : Fin n) (x : ℝⁿ) : ‖x - refll i x‖ = 2 * |x i| := by
  have hxr : x - refll i x = (2 * x i) • EuclideanSpace.single i (1 : ℝ) := by
    rw [refll_apply]
    simp only [reflLin, LinearMap.coe_mk, AddHom.coe_mk]
    abel
  rw [hxr, norm_smul, PiLp.norm_single, Real.norm_eq_abs, norm_one, mul_one, abs_mul]
  norm_num

/-- The reflection-Lipschitz bound on `(evenRefl i u)·φ` needed by `isWeakDerivInDir_glue_normal`:
since the even reflection is `refll`-invariant, the difference is `evenRefl·(φ − φ∘refll)`, and `φ`
smooth gives `|φ − φ∘refll| ≤ C·2|xᵢ|`. -/
theorem evenRefl_reflLipschitz (i : Fin n) {u : ℝⁿ → ℝ} (hu : Continuous u)
    {φ : ℝⁿ → ℝ} (hφ : IsTestFunction Set.univ φ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x, |evenRefl i u x * φ x - evenRefl i u (refll i x) * φ (refll i x)|
      ≤ L * |x i| := by
  have hcont : Continuous (evenRefl i u) := continuous_evenRefl i hu
  obtain ⟨Cf, hCf'⟩ : ∃ C : ℝ, ∀ x, ‖‖fderiv ℝ φ x‖‖ ≤ C :=
    (hφ.contDiff.continuous_fderiv (by norm_num)).norm.bounded_above_of_compact_support
      (hφ.hasCompactSupport.fderiv ℝ).norm
  have hCf : ∀ x, ‖fderiv ℝ φ x‖ ≤ Cf := fun x => by rw [← norm_norm]; exact hCf' x
  have hCf0 : 0 ≤ Cf := (norm_nonneg _).trans (hCf 0)
  have hφdiff : ∀ x, |φ x - φ (refll i x)| ≤ Cf * (2 * |x i|) := by
    intro x
    have h := Convex.norm_image_sub_le_of_norm_fderiv_le (fun z _ => hφ.differentiable z)
      (fun z _ => hCf z) convex_univ (Set.mem_univ x) (Set.mem_univ (refll i x))
    rwa [Real.norm_eq_abs, abs_sub_comm, norm_sub_rev, norm_sub_refll] at h
  obtain ⟨M, hM⟩ := IsCompact.exists_bound_of_continuousOn
    (hφ.hasCompactSupport.sub (hφ.hasCompactSupport.comp_homeomorph (refll i).toHomeomorph))
    hcont.continuousOn
  refine ⟨2 * max M 0 * Cf,
    mul_nonneg (mul_nonneg (by norm_num) (le_max_right _ _)) hCf0, fun x => ?_⟩
  rw [evenRefl_even i u x,
    show evenRefl i u x * φ x - evenRefl i u x * φ (refll i x)
      = evenRefl i u x * (φ x - φ (refll i x)) from by ring, abs_mul]
  by_cases hxs : x ∈ tsupport (fun x => φ x - φ (refll i x))
  · have hev : |evenRefl i u x| ≤ max M 0 := by
      rw [← Real.norm_eq_abs]; exact (hM x hxs).trans (le_max_left _ _)
    calc |evenRefl i u x| * |φ x - φ (refll i x)|
        ≤ (max M 0) * (Cf * (2 * |x i|)) :=
          mul_le_mul hev (hφdiff x) (abs_nonneg _) (le_max_right _ _)
      _ = 2 * max M 0 * Cf * |x i| := by ring
  · rw [image_eq_zero_of_notMem_tsupport hxs, abs_zero, mul_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (le_max_right _ _)) hCf0) (abs_nonneg _)

/-- **The even reflection of a `C¹` function has the reflected weak gradient.** For `u ∈ C¹`, the
even reflection `evenRefl i u` is weakly differentiable in every direction `eⱼ` across `{xᵢ = 0}`,
with derivative the even reflection of `∂ⱼu` for tangential `j` and its odd reflection for `j = i`.
Assembled from the classical derivative on the upper half, the reflection change-of-variables on the
lower half, and the tangential / normal gluing theorems. -/
theorem isWeakDerivInDir_evenRefl (i j : Fin n) {u : ℝⁿ → ℝ} (hu : ContDiff ℝ 1 u) :
    IsWeakDerivInDir Set.univ (EuclideanSpace.single j (1 : ℝ)) (evenRefl i u)
      (fun x => if 0 < x i then fderiv ℝ u x (EuclideanSpace.single j (1 : ℝ))
        else (if j = i then (-1 : ℝ) else 1)
          * fderiv ℝ u (refll i x) (EuclideanSpace.single j (1 : ℝ))) := by
  have hcont : Continuous (evenRefl i u) := continuous_evenRefl i hu.continuous
  have hmsP : MeasurableSet {x : ℝⁿ | 0 < x i} :=
    measurableSet_lt measurable_const (EuclideanSpace.proj i).continuous.measurable
  have hmsN : MeasurableSet {x : ℝⁿ | x i < 0} :=
    measurableSet_lt (EuclideanSpace.proj i).continuous.measurable measurable_const
  have hu_wd : IsWeakDerivInDir Set.univ (EuclideanSpace.single j (1 : ℝ)) u
      (fun x => fderiv ℝ u x (EuclideanSpace.single j (1 : ℝ))) :=
    isWeakDerivInDir_of_contDiff _ _ hu
  have hgp_loc : LocallyIntegrable
      (fun x => fderiv ℝ u x (EuclideanSpace.single j (1 : ℝ))) volume :=
    ((hu.continuous_fderiv (by norm_num)).clm_apply continuous_const).locallyIntegrable
  have hgm_loc : LocallyIntegrable (fun x => (if j = i then (-1 : ℝ) else 1)
      * fderiv ℝ u (refll i x) (EuclideanSpace.single j (1 : ℝ))) volume :=
    (continuous_const.mul
      (((hu.continuous_fderiv (by norm_num)).clm_apply continuous_const).comp
        (contDiff_refll i).continuous)).locallyIntegrable
  have hEu_p : IsWeakDerivInDir {x : ℝⁿ | 0 < x i} (EuclideanSpace.single j (1 : ℝ)) (evenRefl i u)
      (fun x => fderiv ℝ u x (EuclideanSpace.single j (1 : ℝ))) := by
    refine (hu_wd.mono (Set.subset_univ _)).congr_ae_restrict hmsP ?_ Filter.EventuallyEq.rfl
    exact (ae_restrict_iff' hmsP).2 (Filter.Eventually.of_forall
      (fun x hx => (evenRefl_apply_upper i u (le_of_lt hx)).symm))
  have hEu_m : IsWeakDerivInDir {x : ℝⁿ | x i < 0} (EuclideanSpace.single j (1 : ℝ)) (evenRefl i u)
      (fun x => (if j = i then (-1 : ℝ) else 1)
        * fderiv ℝ u (refll i x) (EuclideanSpace.single j (1 : ℝ))) := by
    have hcomp := isWeakDerivInDir_comp_refll i j (hu_wd.mono (Set.subset_univ _))
    refine hcomp.congr_ae_restrict hmsN ?_ Filter.EventuallyEq.rfl
    exact (ae_restrict_iff' hmsN).2 (Filter.Eventually.of_forall
      (fun x hx => (evenRefl_apply_lower i u hx).symm))
  rcases eq_or_ne j i with hji | hji
  · subst hji
    exact isWeakDerivInDir_glue_normal j hcont hgp_loc hgm_loc hEu_p hEu_m
      (fun ψ hψ => evenRefl_reflLipschitz j hu.continuous hψ)
  · exact isWeakDerivInDir_glue_tangential i j hji hcont hgp_loc hgm_loc hEu_p hEu_m



/-- **The even reflection lands in `W^{1,p}(ℝⁿ)` with the reflected weak gradient.** Given a `C¹`
function `u` whose value and each partial derivative are `p`-integrable, its even reflection
`evenRefl i u` is in `W^{1,p}(ℝⁿ)`. The weak gradient is `isWeakDerivInDir_evenRefl`; the `Lᵖ`
memberships follow by splitting into the two half-spaces, using that `refll` preserves Lebesgue
measure (so `∫|evenRefl|ᵖ = 2∫_{xᵢ>0}|u|ᵖ`, and likewise for the reflected gradient). -/
theorem memW1p_evenRefl (i : Fin n) {u : ℝⁿ → ℝ} {p : ℝ≥0∞} (hu : ContDiff ℝ 1 u)
    (hmem : MemLp u p volume)
    (hmemD : ∀ j, MemLp (fun x => fderiv ℝ u x (EuclideanSpace.single j (1 : ℝ))) p volume) :
    MemW1p Set.univ p (evenRefl i u) := by
  have hmsGe : MeasurableSet {x : ℝⁿ | 0 ≤ x i} :=
    measurableSet_le measurable_const (EuclideanSpace.proj i).continuous.measurable
  have hmsLt : MeasurableSet {x : ℝⁿ | x i < 0} :=
    measurableSet_lt (EuclideanSpace.proj i).continuous.measurable measurable_const
  have hmsGt : MeasurableSet {x : ℝⁿ | 0 < x i} :=
    measurableSet_lt measurable_const (EuclideanSpace.proj i).continuous.measurable
  have hmsLe : MeasurableSet {x : ℝⁿ | x i ≤ 0} :=
    measurableSet_le (EuclideanSpace.proj i).continuous.measurable measurable_const
  -- `evenRefl i u ∈ Lᵖ`.
  have hmemE : MemLp (evenRefl i u) p volume := by
    have hmemR : MemLp (fun x => u (refll i x)) p volume :=
      hmem.comp_measurePreserving (refll_measurePreserving i)
    have heq : evenRefl i u = fun x => {x : ℝⁿ | 0 ≤ x i}.indicator u x
        + {x : ℝⁿ | x i < 0}.indicator (fun y => u (refll i y)) x := by
      funext x
      simp only [Set.indicator_apply, Set.mem_setOf_eq]
      by_cases hx : 0 ≤ x i
      · rw [evenRefl_apply_upper i u hx, if_pos hx, if_neg (not_lt.2 hx), add_zero]
      · rw [evenRefl_apply_lower i u (not_le.1 hx), if_neg hx, if_pos (not_le.1 hx), zero_add]
    rw [heq]; exact (hmem.indicator hmsGe).add (hmemR.indicator hmsLt)
  refine ⟨by rw [Measure.restrict_univ]; exact hmemE, fun j => ?_⟩
  refine ⟨fun x => if 0 < x i then fderiv ℝ u x (EuclideanSpace.single j (1 : ℝ))
      else (if j = i then (-1 : ℝ) else 1)
        * fderiv ℝ u (refll i x) (EuclideanSpace.single j (1 : ℝ)),
      isWeakDerivInDir_evenRefl i j hu, ?_⟩
  rw [Measure.restrict_univ]
  have hmemDR : MemLp (fun x => (if j = i then (-1 : ℝ) else 1)
      * fderiv ℝ u (refll i x) (EuclideanSpace.single j (1 : ℝ))) p volume :=
    ((hmemD j).comp_measurePreserving (refll_measurePreserving i)).const_mul _
  have heqv : (fun x => if 0 < x i then fderiv ℝ u x (EuclideanSpace.single j (1 : ℝ))
      else (if j = i then (-1 : ℝ) else 1)
        * fderiv ℝ u (refll i x) (EuclideanSpace.single j (1 : ℝ)))
      = fun x => {x : ℝⁿ | 0 < x i}.indicator
          (fun y => fderiv ℝ u y (EuclideanSpace.single j (1 : ℝ))) x
        + {x : ℝⁿ | x i ≤ 0}.indicator
          (fun y => (if j = i then (-1 : ℝ) else 1)
            * fderiv ℝ u (refll i y) (EuclideanSpace.single j (1 : ℝ))) x := by
    funext x
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    by_cases hx : 0 < x i
    · rw [if_pos hx, if_pos hx, if_neg (not_le.2 hx), add_zero]
    · rw [if_neg hx, if_neg hx, if_pos (not_lt.1 hx), zero_add]
  rw [heqv]
  exact ((hmemD j).indicator hmsGt).add (hmemDR.indicator hmsLe)

/-- **Even reflection lands in `W^{1,p}(ℝⁿ)` from upper-half `Lᵖ` data.**  Variant of
`memW1p_evenRefl` needing `u` and its gradient only in `Lᵖ(\{xᵢ≥0\})` (not whole-space `Lᵖ`) — since
`evenRefl i u` reads `u` solely on the upper half-space.  This is the form the extension operator
uses: an approximant `wₖ` is controlled in `Lᵖ` only over `\{xᵢ>0\}` (by the boundary density), so
whole-space `Lᵖ` (which would need a convolution Young inequality) is unavailable. -/
theorem memW1p_evenRefl_restrict (i : Fin n) {u : ℝⁿ → ℝ} {p : ℝ≥0∞} (hu : ContDiff ℝ 1 u)
    (hmem : MemLp u p (volume.restrict {x : ℝⁿ | 0 ≤ x i}))
    (hmemD : ∀ j, MemLp (fun x => fderiv ℝ u x (EuclideanSpace.single j (1 : ℝ))) p
      (volume.restrict {x : ℝⁿ | 0 ≤ x i})) :
    MemW1p Set.univ p (evenRefl i u) := by
  have hmsGe : MeasurableSet {x : ℝⁿ | 0 ≤ x i} :=
    measurableSet_le measurable_const (EuclideanSpace.proj i).continuous.measurable
  have hmsLt : MeasurableSet {x : ℝⁿ | x i < 0} :=
    measurableSet_lt (EuclideanSpace.proj i).continuous.measurable measurable_const
  have hmsGt : MeasurableSet {x : ℝⁿ | 0 < x i} :=
    measurableSet_lt measurable_const (EuclideanSpace.proj i).continuous.measurable
  have hmsLe : MeasurableSet {x : ℝⁿ | x i ≤ 0} :=
    measurableSet_le (EuclideanSpace.proj i).continuous.measurable measurable_const
  have hsubGt : volume.restrict {x : ℝⁿ | 0 < x i} ≤ volume.restrict {x : ℝⁿ | 0 ≤ x i} :=
    Measure.restrict_mono (Set.setOf_subset_setOf.2 (fun _ hx => hx.le)) le_rfl
  -- measure-preserving reflections between the restricted half-spaces
  have hpre1 : refll i ⁻¹' {x : ℝⁿ | 0 < x i} = {x : ℝⁿ | x i < 0} := by
    ext x; simp only [Set.mem_preimage, Set.mem_setOf_eq, refll_apply_self]
    constructor <;> intro h <;> linarith
  have hmp1 : MeasurePreserving (refll i) (volume.restrict {x : ℝⁿ | x i < 0})
      (volume.restrict {x : ℝⁿ | 0 < x i}) := by
    have h := (refll_measurePreserving i).restrict_preimage hmsGt; rwa [hpre1] at h
  have hpre2 : refll i ⁻¹' {x : ℝⁿ | 0 ≤ x i} = {x : ℝⁿ | x i ≤ 0} := by
    ext x; simp only [Set.mem_preimage, Set.mem_setOf_eq, refll_apply_self]
    constructor <;> intro h <;> linarith
  have hmp2 : MeasurePreserving (refll i) (volume.restrict {x : ℝⁿ | x i ≤ 0})
      (volume.restrict {x : ℝⁿ | 0 ≤ x i}) := by
    have h := (refll_measurePreserving i).restrict_preimage hmsGe; rwa [hpre2] at h
  -- `evenRefl i u ∈ Lᵖ`.
  have hmemE : MemLp (evenRefl i u) p volume := by
    have hmemR : MemLp (fun x => u (refll i x)) p (volume.restrict {x : ℝⁿ | x i < 0}) :=
      (hmem.mono_measure hsubGt).comp_measurePreserving hmp1
    have heq : evenRefl i u = fun x => {x : ℝⁿ | 0 ≤ x i}.indicator u x
        + {x : ℝⁿ | x i < 0}.indicator (fun y => u (refll i y)) x := by
      funext x
      simp only [Set.indicator_apply, Set.mem_setOf_eq]
      by_cases hx : 0 ≤ x i
      · rw [evenRefl_apply_upper i u hx, if_pos hx, if_neg (not_lt.2 hx), add_zero]
      · rw [evenRefl_apply_lower i u (not_le.1 hx), if_neg hx, if_pos (not_le.1 hx), zero_add]
    rw [heq]
    exact ((memLp_indicator_iff_restrict hmsGe).2 hmem).add
      ((memLp_indicator_iff_restrict hmsLt).2 hmemR)
  refine ⟨by rw [Measure.restrict_univ]; exact hmemE, fun j => ?_⟩
  refine ⟨fun x => if 0 < x i then fderiv ℝ u x (EuclideanSpace.single j (1 : ℝ))
      else (if j = i then (-1 : ℝ) else 1)
        * fderiv ℝ u (refll i x) (EuclideanSpace.single j (1 : ℝ)),
      isWeakDerivInDir_evenRefl i j hu, ?_⟩
  rw [Measure.restrict_univ]
  have hmemDR : MemLp (fun x => (if j = i then (-1 : ℝ) else 1)
      * fderiv ℝ u (refll i x) (EuclideanSpace.single j (1 : ℝ))) p
      (volume.restrict {x : ℝⁿ | x i ≤ 0}) :=
    ((hmemD j).comp_measurePreserving hmp2).const_mul _
  have heqv : (fun x => if 0 < x i then fderiv ℝ u x (EuclideanSpace.single j (1 : ℝ))
      else (if j = i then (-1 : ℝ) else 1)
        * fderiv ℝ u (refll i x) (EuclideanSpace.single j (1 : ℝ)))
      = fun x => {x : ℝⁿ | 0 < x i}.indicator
          (fun y => fderiv ℝ u y (EuclideanSpace.single j (1 : ℝ))) x
        + {x : ℝⁿ | x i ≤ 0}.indicator
          (fun y => (if j = i then (-1 : ℝ) else 1)
            * fderiv ℝ u (refll i y) (EuclideanSpace.single j (1 : ℝ))) x := by
    funext x
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    by_cases hx : 0 < x i
    · rw [if_pos hx, if_pos hx, if_neg (not_le.2 hx), add_zero]
    · rw [if_neg hx, if_neg hx, if_pos (not_lt.1 hx), zero_add]
  rw [heqv]
  exact ((memLp_indicator_iff_restrict hmsGt).2 ((hmemD j).mono_measure hsubGt)).add
    ((memLp_indicator_iff_restrict hmsLe).2 hmemDR)



/-- The even reflection is additive. -/
theorem evenRefl_add (i : Fin n) (u v : ℝⁿ → ℝ) :
    evenRefl i (fun x => u x + v x) = fun x => evenRefl i u x + evenRefl i v x := by
  funext x; simp only [evenRefl]; split_ifs <;> rfl

/-- The even reflection is homogeneous. -/
theorem evenRefl_smul (i : Fin n) (c : ℝ) (u : ℝⁿ → ℝ) :
    evenRefl i (fun x => c * u x) = fun x => c * evenRefl i u x := by
  funext x; simp only [evenRefl]; split_ifs <;> rfl

/-- **Lᵖ operator bound for the even reflection.** `‖evenRefl i u‖_p ≤ 2‖u‖_p`, so the reflection
extension is a bounded operator on `Lᵖ` (`1 ≤ p`). Proof: `evenRefl` splits as the sum of `u` and
`u ∘ refll` restricted to the two half-spaces; the triangle inequality, the indicator bound, and the
`refll`-invariance of the `Lᵖ` norm give the factor `2`. -/
theorem eLpNorm_evenRefl_le (i : Fin n) {u : ℝⁿ → ℝ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hu : AEStronglyMeasurable u volume) :
    eLpNorm (evenRefl i u) p volume ≤ 2 * eLpNorm u p volume := by
  have hmsGe : MeasurableSet {x : ℝⁿ | 0 ≤ x i} :=
    measurableSet_le measurable_const (EuclideanSpace.proj i).continuous.measurable
  have hmsLt : MeasurableSet {x : ℝⁿ | x i < 0} :=
    measurableSet_lt (EuclideanSpace.proj i).continuous.measurable measurable_const
  have heq : evenRefl i u = fun x => {x : ℝⁿ | 0 ≤ x i}.indicator u x
      + {x : ℝⁿ | x i < 0}.indicator (fun y => u (refll i y)) x := by
    funext x
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    by_cases hx : 0 ≤ x i
    · rw [evenRefl_apply_upper i u hx, if_pos hx, if_neg (not_lt.2 hx), add_zero]
    · rw [evenRefl_apply_lower i u (not_le.1 hx), if_neg hx, if_pos (not_le.1 hx), zero_add]
  have hAr : AEStronglyMeasurable (fun y => u (refll i y)) volume :=
    hu.comp_measurePreserving (refll_measurePreserving i)
  have hcomp : eLpNorm (fun y => u (refll i y)) p volume = eLpNorm u p volume :=
    eLpNorm_comp_measurePreserving hu (refll_measurePreserving i)
  rw [heq]
  calc eLpNorm (fun x => {x : ℝⁿ | 0 ≤ x i}.indicator u x
        + {x : ℝⁿ | x i < 0}.indicator (fun y => u (refll i y)) x) p volume
      ≤ eLpNorm ({x : ℝⁿ | 0 ≤ x i}.indicator u) p volume
        + eLpNorm ({x : ℝⁿ | x i < 0}.indicator (fun y => u (refll i y))) p volume :=
        eLpNorm_add_le (hu.indicator hmsGe) (hAr.indicator hmsLt) hp
    _ ≤ eLpNorm u p volume + eLpNorm (fun y => u (refll i y)) p volume :=
        add_le_add (eLpNorm_indicator_le u) (eLpNorm_indicator_le _)
    _ = 2 * eLpNorm u p volume := by rw [hcomp, two_mul]

/-- **Restricted `Lᵖ` bound for the even reflection.**  Since `evenRefl i u` reads `u` only on
`{xᵢ≥0}`, one has `evenRefl i u = evenRefl i (1_{xᵢ≥0}·u)`, so the whole-space bound applied to the
zero-extension gives `‖evenRefl i u‖_{Lᵖ(ℝⁿ)} ≤ 2‖u‖_{Lᵖ(\{xᵢ≥0\})}` — the norm measured only on the
upper half-space.  This is the form the bounded-extension-by-density argument needs (the `{xᵢ<0}`
values of an approximant never enter). -/
theorem eLpNorm_evenRefl_le_restrict (i : Fin n) {u : ℝⁿ → ℝ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hu : AEStronglyMeasurable u volume) :
    eLpNorm (evenRefl i u) p volume ≤ 2 * eLpNorm u p (volume.restrict {x : ℝⁿ | 0 ≤ x i}) := by
  have hmsGe : MeasurableSet {x : ℝⁿ | 0 ≤ x i} :=
    measurableSet_le measurable_const (EuclideanSpace.proj i).continuous.measurable
  have hind : evenRefl i u = evenRefl i ({x : ℝⁿ | 0 ≤ x i}.indicator u) := by
    funext x
    by_cases hx : 0 ≤ x i
    · rw [evenRefl_apply_upper i u hx, evenRefl_apply_upper i _ hx,
        Set.indicator_of_mem (show x ∈ {x : ℝⁿ | 0 ≤ x i} from hx)]
    · rw [evenRefl_apply_lower i u (not_le.1 hx), evenRefl_apply_lower i _ (not_le.1 hx),
        Set.indicator_of_mem (show refll i x ∈ {x : ℝⁿ | 0 ≤ x i} by
          simp only [Set.mem_setOf_eq, refll_apply_self]; linarith [not_le.1 hx])]
  rw [hind]
  calc eLpNorm (evenRefl i ({x : ℝⁿ | 0 ≤ x i}.indicator u)) p volume
      ≤ 2 * eLpNorm ({x : ℝⁿ | 0 ≤ x i}.indicator u) p volume :=
        eLpNorm_evenRefl_le i hp (hu.indicator hmsGe)
    _ = 2 * eLpNorm u p (volume.restrict {x : ℝⁿ | 0 ≤ x i}) := by
        rw [eLpNorm_indicator_eq_eLpNorm_restrict hmsGe]



/-- Abstract `Lᵖ` bound for a normal-glue-shaped function `x ↦ if 0 < xᵢ then g x else B x`, when
the lower branch `B` has the same `Lᵖ` norm as `g`.  Stated over abstract `g, B` so the elaborator
never unfolds `eLpNorm` on the concrete reflected-derivative terms of the application. -/
theorem eLpNorm_normalGlue_le (i : Fin n) {p : ℝ≥0∞} (hp : 1 ≤ p) {g B : ℝⁿ → ℝ}
    (hg : AEStronglyMeasurable g volume) (hB : AEStronglyMeasurable B volume)
    (hBg : eLpNorm B p volume = eLpNorm g p volume) :
    eLpNorm (fun x => if 0 < x i then g x else B x) p volume ≤ 2 * eLpNorm g p volume := by
  have hmsGt : MeasurableSet {x : ℝⁿ | 0 < x i} :=
    measurableSet_lt measurable_const (EuclideanSpace.proj i).continuous.measurable
  have hmsLe : MeasurableSet {x : ℝⁿ | x i ≤ 0} :=
    measurableSet_le (EuclideanSpace.proj i).continuous.measurable measurable_const
  have heqv : (fun x => if 0 < x i then g x else B x)
      = fun x => {x : ℝⁿ | 0 < x i}.indicator g x + {x : ℝⁿ | x i ≤ 0}.indicator B x := by
    funext x
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    by_cases hx : 0 < x i
    · rw [if_pos hx, if_pos hx, if_neg (not_le.2 hx), add_zero]
    · rw [if_neg hx, if_neg hx, if_pos (not_lt.1 hx), zero_add]
  rw [heqv]
  calc eLpNorm (fun x => {x : ℝⁿ | 0 < x i}.indicator g x
          + {x : ℝⁿ | x i ≤ 0}.indicator B x) p volume
      ≤ eLpNorm ({x : ℝⁿ | 0 < x i}.indicator g) p volume
        + eLpNorm ({x : ℝⁿ | x i ≤ 0}.indicator B) p volume :=
        eLpNorm_add_le (hg.indicator hmsGt) (hB.indicator hmsLe) hp
    _ ≤ eLpNorm g p volume + eLpNorm B p volume :=
        add_le_add (eLpNorm_indicator_le g) (eLpNorm_indicator_le B)
    _ = 2 * eLpNorm g p volume := by rw [hBg, two_mul]

/-- **Lᵖ operator bound for the even reflection's weak gradient.** The reflected `eⱼ`-derivative of
`evenRefl i u` (from `isWeakDerivInDir_evenRefl`) has `Lᵖ` norm at most `2‖∂ⱼu‖_p`.  The reflected
lower branch is rewritten into composition form `(·) ∘ refll` *before* any `eLpNorm` step, so
`refll` never leaks into an `eLpNorm` defeq check (which otherwise diverges). -/
theorem eLpNorm_evenRefl_grad_le (i j : Fin n) {u : ℝⁿ → ℝ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hg : AEStronglyMeasurable
      (fun x => fderiv ℝ u x (EuclideanSpace.single j (1 : ℝ))) volume) :
    eLpNorm (fun x => if 0 < x i then fderiv ℝ u x (EuclideanSpace.single j (1 : ℝ))
        else (if j = i then (-1 : ℝ) else 1)
          * fderiv ℝ u (refll i x) (EuclideanSpace.single j (1 : ℝ))) p volume
      ≤ 2 * eLpNorm (fun x => fderiv ℝ u x (EuclideanSpace.single j (1 : ℝ))) p volume := by
  have hB : AEStronglyMeasurable (fun x => (if j = i then (-1 : ℝ) else 1)
      * fderiv ℝ u (refll i x) (EuclideanSpace.single j (1 : ℝ))) volume :=
    (hg.comp_measurePreserving (refll_measurePreserving i)).const_mul _
  have hBnorm : eLpNorm (fun x => (if j = i then (-1 : ℝ) else 1)
        * fderiv ℝ u (refll i x) (EuclideanSpace.single j (1 : ℝ))) p volume
      = eLpNorm (fun x => fderiv ℝ u x (EuclideanSpace.single j (1 : ℝ))) p volume := by
    have hfun : (fun x => (if j = i then (-1 : ℝ) else 1)
          * fderiv ℝ u (refll i x) (EuclideanSpace.single j (1 : ℝ)))
        = (fun y => (if j = i then (-1 : ℝ) else 1)
          * fderiv ℝ u y (EuclideanSpace.single j (1 : ℝ))) ∘ refll i := rfl
    rw [hfun, eLpNorm_comp_measurePreserving (hg.const_mul _) (refll_measurePreserving i)]
    split_ifs with h
    · simp only [neg_one_mul]
      exact eLpNorm_neg (fun y => fderiv ℝ u y (EuclideanSpace.single j (1 : ℝ))) p volume
    · simp only [one_mul]
  exact eLpNorm_normalGlue_le i hp hg hB hBnorm



/-- **Linear change of variables for weak derivatives.** For a linear isometry `L` of `ℝⁿ`, if `v`
is the weak `(L e)`-derivative of `u`, then `v ∘ L` is the weak `e`-derivative of `u ∘ L`.  This
generalizes `isWeakDerivInDir_comp_refll` (the reflection case) to an arbitrary linear isometry: the
substitution `x = L⁻¹ y`, which preserves Lebesgue measure, together with the chain rule
`∂_e(φ ∘ L⁻¹) = ∂_{L e}φ ∘ L⁻¹`, transports the weak-derivative identity through `L`. -/
theorem isWeakDerivInDir_comp_linear (L : ℝⁿ ≃ₗᵢ[ℝ] ℝⁿ) (e : ℝⁿ) {u v : ℝⁿ → ℝ}
    (h : IsWeakDerivInDir Set.univ (L e) u v) :
    IsWeakDerivInDir Set.univ e (fun x => u (L x)) (fun x => v (L x)) := by
  intro φ hφ
  simp only []
  have hLmp : MeasurePreserving (L : ℝⁿ → ℝⁿ) volume volume := L.measurePreserving
  have hLme : MeasurableEmbedding (L : ℝⁿ → ℝⁿ) := L.toHomeomorph.measurableEmbedding
  have hinvsymm : ∀ x, L.symm (L x) = x := L.symm_apply_apply
  -- `ψ = φ ∘ L.symm` is a test function.
  have hψ : IsTestFunction Set.univ (fun z => φ (L.symm z)) :=
    ⟨hφ.contDiff.comp L.symm.toContinuousLinearEquiv.contDiff,
      hφ.hasCompactSupport.comp_homeomorph L.symm.toHomeomorph, Set.subset_univ _⟩
  -- Chain rule: `∂_e φ` at `L.symm y` equals `∂_{L e}ψ` at `y`.
  have hpt : ∀ y, fderiv ℝ φ (L.symm y) e
      = fderiv ℝ (fun z => φ (L.symm z)) y (L e) := by
    intro y
    have hcomp : HasFDerivAt (fun z => φ (L.symm z))
        ((fderiv ℝ φ (L.symm y)).comp
          (L.symm.toContinuousLinearEquiv : ℝⁿ →L[ℝ] ℝⁿ)) y :=
      (hφ.differentiable (L.symm y)).hasFDerivAt.comp y
        L.symm.toContinuousLinearEquiv.hasFDerivAt
    rw [hcomp.fderiv, ContinuousLinearMap.comp_apply]
    change fderiv ℝ φ (L.symm y) e = fderiv ℝ φ (L.symm y) (L.symm (L e))
    rw [hinvsymm e]
  -- Change variables `x = L.symm y` on both sides via measure-preservation of `L`.
  have hcovL : ∫ x, u (L x) * fderiv ℝ φ x e
      = ∫ y, u y * fderiv ℝ φ (L.symm y) e := by
    have key := hLmp.integral_comp hLme (fun y => u y * fderiv ℝ φ (L.symm y) e)
    simp only [hinvsymm] at key
    exact key
  have hcovR : ∫ x, v (L x) * φ x = ∫ y, v y * φ (L.symm y) := by
    have key := hLmp.integral_comp hLme (fun y => v y * φ (L.symm y))
    simp only [hinvsymm] at key
    exact key
  rw [hcovL,
    show (∫ y, u y * fderiv ℝ φ (L.symm y) e)
      = ∫ y, u y * fderiv ℝ (fun z => φ (L.symm z)) y (L e) from
      integral_congr_ae (Filter.Eventually.of_forall (fun y => by simp only [hpt y])),
    h _ hψ, ← hcovR]



/-- **`W^{1,p}(ℝⁿ)` is invariant under a coordinate reflection.** If `u ∈ W^{1,p}(ℝⁿ)` then so is
`u ∘ refll i`.  Assembled from the linear change of variables `isWeakDerivInDir_comp_linear`, the
direction-scaling `IsWeakDerivInDir.dir_smul` (since `refll` sends `eⱼ ↦ ±eⱼ`), and the
`refll`-invariance of the `Lᵖ` norm. -/
theorem MemW1p.comp_refll (i : Fin n) {p : ℝ≥0∞} {u : ℝⁿ → ℝ} (hu : MemW1p Set.univ p u) :
    MemW1p Set.univ p (fun x => u (refll i x)) := by
  have hmu : MemLp u p volume := by
    rw [← Measure.restrict_univ (μ := (volume : Measure ℝⁿ))]; exact hu.memLp
  refine ⟨?_, fun j => ?_⟩
  · rw [Measure.restrict_univ]
    exact hmu.comp_measurePreserving (refll_measurePreserving i)
  · obtain ⟨vⱼ, hvⱼ, hvⱼLp⟩ := hu.exists_weakDeriv j
    have hmvj : MemLp vⱼ p volume := by
      rw [← Measure.restrict_univ (μ := (volume : Measure ℝⁿ))]; exact hvⱼLp
    have hd : IsWeakDerivInDir Set.univ (refll i (EuclideanSpace.single j (1 : ℝ))) u
        (fun x => (if j = i then (-1 : ℝ) else 1) * vⱼ x) := by
      rw [refll_single]
      exact hvⱼ.dir_smul (if j = i then (-1 : ℝ) else 1)
    refine ⟨fun x => (if j = i then (-1 : ℝ) else 1) * vⱼ (refll i x), ?_, ?_⟩
    · exact isWeakDerivInDir_comp_linear (refll i) (EuclideanSpace.single j (1 : ℝ)) hd
    · rw [Measure.restrict_univ]
      exact (hmvj.comp_measurePreserving (refll_measurePreserving i)).const_mul _



/-- **Translation invariance of the weak derivative.** If `v` is the weak `e`-derivative of `u`,
then `v(· + t)` is the weak `e`-derivative of `u(· + t)`.  The affine analogue of
`isWeakDerivInDir_comp_linear`: translation is measure-preserving and its derivative is the
identity, so the direction is unchanged.  A building block for `Lᵖ`/`W^{1,p}` translation-continuity
(the boundary-density argument for the half-space extension). -/
theorem isWeakDerivInDir_comp_translate (t : ℝⁿ) (e : ℝⁿ) {u v : ℝⁿ → ℝ}
    (h : IsWeakDerivInDir Set.univ e u v) :
    IsWeakDerivInDir Set.univ e (fun x => u (x + t)) (fun x => v (x + t)) := by
  intro φ hφ
  simp only []
  have hmp : MeasurePreserving (fun x : ℝⁿ => x + t) volume volume :=
    measurePreserving_add_right volume t
  have hme : MeasurableEmbedding (fun x : ℝⁿ => x + t) :=
    (Homeomorph.addRight t).measurableEmbedding
  -- `ψ = φ(· - t)` is a test function.
  have hψ : IsTestFunction Set.univ (fun z => φ (z - t)) :=
    ⟨hφ.contDiff.comp ((contDiff_id).sub contDiff_const),
      hφ.hasCompactSupport.comp_homeomorph (Homeomorph.subRight t), Set.subset_univ _⟩
  -- Chain rule: `∂_e φ` at `y - t` equals `∂_e ψ` at `y` (translation derivative is the identity).
  have hpt : ∀ y, fderiv ℝ φ (y - t) e = fderiv ℝ (fun z => φ (z - t)) y e := by
    intro y
    have hcomp : HasFDerivAt (fun z => φ (z - t)) (fderiv ℝ φ (y - t)) y := by
      have := (hφ.differentiable (y - t)).hasFDerivAt.comp y
        ((hasFDerivAt_id y).sub_const t)
      simpa using this
    rw [hcomp.fderiv]
  -- Change variables `x = y - t` on both sides via measure-preservation of translation.
  have hcovL : ∫ x, u (x + t) * fderiv ℝ φ x e = ∫ y, u y * fderiv ℝ φ (y - t) e := by
    have key := hmp.integral_comp hme (fun y => u y * fderiv ℝ φ (y - t) e)
    simp only [add_sub_cancel_right] at key
    exact key
  have hcovR : ∫ x, v (x + t) * φ x = ∫ y, v y * φ (y - t) := by
    have key := hmp.integral_comp hme (fun y => v y * φ (y - t))
    simp only [add_sub_cancel_right] at key
    exact key
  rw [hcovL,
    show (∫ y, u y * fderiv ℝ φ (y - t) e)
      = ∫ y, u y * fderiv ℝ (fun z => φ (z - t)) y e from
      integral_congr_ae (Filter.Eventually.of_forall (fun y => by simp only [hpt y])),
    h _ hψ, ← hcovR]




/-- **`W^{1,p}(ℝⁿ)` is invariant under translation.** -/
theorem MemW1p.comp_translate (t : ℝⁿ) {p : ℝ≥0∞} {u : ℝⁿ → ℝ} (hu : MemW1p Set.univ p u) :
    MemW1p Set.univ p (fun x => u (x + t)) := by
  have hmu : MemLp u p volume := by
    rw [← Measure.restrict_univ (μ := (volume : Measure ℝⁿ))]; exact hu.memLp
  refine ⟨?_, fun j => ?_⟩
  · rw [Measure.restrict_univ]
    exact hmu.comp_measurePreserving (measurePreserving_add_right volume t)
  · obtain ⟨vⱼ, hvⱼ, hvⱼLp⟩ := hu.exists_weakDeriv j
    have hmvj : MemLp vⱼ p volume := by
      rw [← Measure.restrict_univ (μ := (volume : Measure ℝⁿ))]; exact hvⱼLp
    refine ⟨fun x => vⱼ (x + t),
      isWeakDerivInDir_comp_translate t (EuclideanSpace.single j (1 : ℝ)) hvⱼ, ?_⟩
    rw [Measure.restrict_univ]
    exact hmvj.comp_measurePreserving (measurePreserving_add_right volume t)

/-- **Translation is continuous in `W^{1,p}`** (`1 ≤ p < ∞`): as `t → 0`, both `u(· + t) → u` and
each weak derivative `vⱼ(· + t) → vⱼ` in `Lᵖ`, so the total `W^{1,p}`-seminorm error → `0`.  The
engine of the boundary-density argument for the half-space extension; it bundles the `Lᵖ`
translation-continuity `tendsto_eLpNorm_translate_sub` over `u` and all `n` derivatives. -/
theorem tendsto_eLpNorm_translate_memW1p {u : ℝⁿ → ℝ} {v : Fin n → ℝⁿ → ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hu : MemLp u p volume) (hv : ∀ j, MemLp (v j) p volume) :
    Tendsto (fun t : ℝⁿ => eLpNorm (fun x => u (x + t) - u x) p volume
        + ∑ j, eLpNorm (fun x => v j (x + t) - v j x) p volume) (𝓝 0) (𝓝 0) := by
  have hfunc : Tendsto (fun t : ℝⁿ => eLpNorm (fun x => u (x + t) - u x) p volume) (𝓝 0) (𝓝 0) :=
    tendsto_eLpNorm_translate_sub hp hu
  have hsum : Tendsto (fun t : ℝⁿ => ∑ j, eLpNorm (fun x => v j (x + t) - v j x) p volume)
      (𝓝 0) (𝓝 0) := by
    have := tendsto_finset_sum (Finset.univ : Finset (Fin n))
      (fun j _ => tendsto_eLpNorm_translate_sub hp (hv j))
    simpa using this
  simpa using hfunc.add hsum

/-- **Restricted `Lᵖ` translation-continuity toward the boundary.** For `u ∈ Lᵖ({xᵢ > 0})`, shifting
into the interior along `+eᵢ` converges in `Lᵖ({xᵢ > 0})`: `‖u(· + s·eᵢ) − u‖_{Lᵖ({xᵢ>0})} → 0` as
`s ↓ 0`.  Proved by extending `u` by `0` to `ℝⁿ` (`= S.indicator u ∈ Lᵖ(ℝⁿ)`), applying the
whole-space translation-continuity, and squeezing (the restricted norm is `≤` the whole-space one,
and on `{xᵢ>0}` the shift `s > 0` keeps the argument inside `{xᵢ>0}` where the extension equals `u`).
The boundary-density engine for the half-space extension. -/
theorem tendsto_eLpNorm_translate_sub_restrict_pos (i : Fin n) {u : ℝⁿ → ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hu : MemLp u p (volume.restrict {x : ℝⁿ | 0 < x i})) :
    Tendsto (fun s : ℝ => eLpNorm (fun x => u (x + s • EuclideanSpace.single i (1 : ℝ)) - u x) p
      (volume.restrict {x : ℝⁿ | 0 < x i})) (𝓝[>] 0) (𝓝 0) := by
  have hmsGt : MeasurableSet {x : ℝⁿ | 0 < x i} :=
    measurableSet_lt measurable_const (EuclideanSpace.proj i).continuous.measurable
  set S : Set ℝⁿ := {x : ℝⁿ | 0 < x i} with hS
  have hũ : MemLp (S.indicator u) p volume := (memLp_indicator_iff_restrict hmsGt).2 hu
  -- coordinate fact: for `x i > 0` and `s > 0`, `(x + s • eᵢ) ∈ S`.
  have hmem : ∀ {x : ℝⁿ} {s : ℝ}, 0 < x i → 0 < s → x + s • EuclideanSpace.single i (1 : ℝ) ∈ S := by
    intro x s hx hs
    have hcoord : (x + s • EuclideanSpace.single i (1 : ℝ)) i = x i + s := by
      simp [PiLp.add_apply, PiLp.smul_apply]
    simp only [hS, Set.mem_setOf_eq, hcoord]
    linarith
  -- whole-space translation-continuity for the extension, composed with `s ↦ s • eᵢ`.
  have hwhole : Tendsto (fun s : ℝ => eLpNorm
      (fun x => S.indicator u (x + s • EuclideanSpace.single i (1 : ℝ)) - S.indicator u x) p volume)
      (𝓝 0) (𝓝 0) := by
    have h2 : Tendsto (fun s : ℝ => s • EuclideanSpace.single i (1 : ℝ)) (𝓝 0) (𝓝 0) := by
      have hc : Continuous (fun s : ℝ => s • EuclideanSpace.single i (1 : ℝ)) :=
        continuous_id.smul continuous_const
      simpa only [zero_smul] using hc.tendsto 0
    exact (tendsto_eLpNorm_translate_sub hp hũ).comp h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (hwhole.mono_left nhdsWithin_le_nhds)
    (Filter.Eventually.of_forall (fun s => zero_le _)) ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : (0 : ℝ) < s)
  have hcongr : eLpNorm (fun x => u (x + s • EuclideanSpace.single i (1 : ℝ)) - u x) p
        (volume.restrict S)
      = eLpNorm (fun x => S.indicator u (x + s • EuclideanSpace.single i (1 : ℝ))
        - S.indicator u x) p (volume.restrict S) := by
    refine eLpNorm_congr_ae ((ae_restrict_iff' hmsGt).2 (Filter.Eventually.of_forall
      (fun x (hx : 0 < x i) => ?_)))
    show u (x + s • EuclideanSpace.single i (1 : ℝ)) - u x
        = S.indicator u (x + s • EuclideanSpace.single i (1 : ℝ)) - S.indicator u x
    rw [Set.indicator_of_mem (hmem hx hs), Set.indicator_of_mem (show x ∈ S from hx)]
  rw [hcongr]
  exact eLpNorm_mono_measure _ Measure.restrict_le_self

/-- **Restricted `W^{1,p}` translation-continuity toward the boundary.**  Packaging
`tendsto_eLpNorm_translate_sub_restrict_pos` over the function together with each of its weak-gradient
components: as the inward shift `s ↓ 0`, the full `W^{1,p}({xᵢ>0})` translation increment
`‖u(·+s·eᵢ)−u‖ + ∑ⱼ‖vⱼ(·+s·eᵢ)−vⱼ‖` tends to `0`.  This is the translation half of the
mollification-up-to-the-boundary density for the half-space, mirroring the whole-space
`tendsto_eLpNorm_translate_memW1p`. -/
theorem tendsto_eLpNorm_translate_restrict_memW1p (i : Fin n) {u : ℝⁿ → ℝ} {v : Fin n → ℝⁿ → ℝ}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (hu : MemLp u p (volume.restrict {x : ℝⁿ | 0 < x i}))
    (hv : ∀ j, MemLp (v j) p (volume.restrict {x : ℝⁿ | 0 < x i})) :
    Tendsto (fun s : ℝ =>
        eLpNorm (fun x => u (x + s • EuclideanSpace.single i (1 : ℝ)) - u x) p
          (volume.restrict {x : ℝⁿ | 0 < x i})
        + ∑ j, eLpNorm (fun x => v j (x + s • EuclideanSpace.single i (1 : ℝ)) - v j x) p
          (volume.restrict {x : ℝⁿ | 0 < x i})) (𝓝[>] 0) (𝓝 0) := by
  have hfunc := tendsto_eLpNorm_translate_sub_restrict_pos i hp hu
  have hsum : Tendsto (fun s : ℝ => ∑ j, eLpNorm
      (fun x => v j (x + s • EuclideanSpace.single i (1 : ℝ)) - v j x) p
      (volume.restrict {x : ℝⁿ | 0 < x i})) (𝓝[>] 0) (𝓝 0) := by
    have := tendsto_finset_sum (Finset.univ : Finset (Fin n))
      (fun j _ => tendsto_eLpNorm_translate_sub_restrict_pos i hp (hv j))
    simpa using this
  simpa using hfunc.add hsum

/-- **Restricted `Lᵖ` mollification error.**  For `u ∈ Lᵖ(ℝⁿ)` and any set `S`, the mollification
error measured on `S` vanishes: `‖ρ_η ⋆ u − u‖_{Lᵖ(S)} → 0` as the mollifier radius `→ 0`.  Immediate
from the whole-space error `tendsto_eLpNorm_convolution_sub` by the monotonicity of `eLpNorm` under
`volume.restrict S ≤ volume`.  This supplies the `Lᵖ` half of the mollification-up-to-the-boundary
density on `S = {xᵢ>0}`. -/
theorem tendsto_eLpNorm_convolution_sub_restrict {u : ℝⁿ → ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (hu : MemLp u p volume) (S : Set ℝⁿ) {ι : Type*} {l : Filter ι}
    {φ : ι → ContDiffBump (0 : ℝⁿ)} (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0)) :
    Tendsto (fun i => eLpNorm
      (fun x => ((φ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x - u x) p
        (volume.restrict S)) l (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_eLpNorm_convolution_sub hp hu hφ)
    (Filter.Eventually.of_forall fun _ => zero_le _)
    (Filter.Eventually.of_forall fun _ => eLpNorm_mono_measure _ Measure.restrict_le_self)

/-- **Localized commutation identity: the derivative passes through the convolution onto a
weak derivative valid only on an open set `U`.**  The whole-space `convolution_deriv_eq` needs
`IsWeakDerivInDir univ e u v`; but the reflected mollifier `z ↦ η(x−z)` used to prove it is a test
function supported in `x − supp η`, so the identity `(∂ₑη) ⋆ u = η ⋆ v` at the point `x` needs only
that this support sits inside the set where `u` genuinely has its weak derivative.  This is the tool
that lets the mollification of an *inward-shifted* half-space function sample only the interior
`{xᵢ>0}` — the gradient half of the boundary density.  Proof is the whole-space one with the single
change `subset_univ _ ↦ hUsupp`. -/
lemma convolution_deriv_eq_of_subset {η : ℝⁿ → ℝ} (hη : ContDiff ℝ ∞ η)
    (hηsupp : HasCompactSupport η) {U : Set ℝⁿ} {u v : ℝⁿ → ℝ} (e : ℝⁿ)
    (hweak : IsWeakDerivInDir U e u v) (x : ℝⁿ) (hUsupp : tsupport (fun z => η (x - z)) ⊆ U) :
    ((fun z => fderiv ℝ η z e) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x
      = (η ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) x := by
  set φ : ℝⁿ → ℝ := fun z => η (x - z) with hφdef
  have hφ_cd : ContDiff ℝ ∞ φ := hη.comp (contDiff_const.sub contDiff_id)
  have hφ_cs : HasCompactSupport φ := hηsupp.comp_homeomorph (Homeomorph.subLeft x)
  have hφ_test : IsTestFunction U φ := ⟨hφ_cd, hφ_cs, hUsupp⟩
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
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have hw := hweak φ hφ_test
  calc ∫ t, fderiv ℝ η (x - t) e * u t ∂volume
      = ∫ t, u t * fderiv ℝ η (x - t) e ∂volume :=
        integral_congr_ae (Filter.Eventually.of_forall fun t => mul_comm _ _)
    _ = -∫ t, u t * fderiv ℝ φ t e ∂volume := by
        simp_rw [hchain, mul_neg, integral_neg, neg_neg]
    _ = - -∫ t, v t * φ t ∂volume := by rw [hw]
    _ = ∫ t, η (x - t) * v t ∂volume := by
        rw [neg_neg]
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        change v t * φ t = η (x - t) * v t
        simp only [hφdef]; ring

/-- **The weak-derivative relation depends only on the values on `U`.**  A test function for `U` is
supported inside `U`, so the defining identity `∫ u·∂ₑφ = −∫ v·φ` only samples `u, v` on `U`.  Hence
if `u', v'` agree with `u, v` throughout `U`, they inherit the same weak derivative on `U`.  This lets
the zero-extension `ũ = 1_{xᵢ>0}·u` carry `u`'s weak derivative on the open half-space `{xᵢ>0}`. -/
lemma IsWeakDerivInDir.congr_eqOn {U : Set ℝⁿ} {e : ℝⁿ} {u v u' v' : ℝⁿ → ℝ}
    (h : IsWeakDerivInDir U e u v) (hu : Set.EqOn u' u U) (hv : Set.EqOn v' v U) :
    IsWeakDerivInDir U e u' v' := by
  intro φ hφ
  -- outside `tsupport φ ⊆ U` both `φ` and `∂ₑφ` vanish
  have hfd0 : ∀ x, x ∉ tsupport φ → fderiv ℝ φ x e = 0 := by
    intro x hx
    have hev : φ =ᶠ[𝓝 x] (fun _ => 0) := notMem_tsupport_iff_eventuallyEq.mp hx
    simp [hev.fderiv_eq]
  have hφ0 : ∀ x, x ∉ tsupport φ → φ x = 0 :=
    fun x hx => (notMem_tsupport_iff_eventuallyEq.mp hx).eq_of_nhds
  have hL : ∫ x, u' x * fderiv ℝ φ x e = ∫ x, u x * fderiv ℝ φ x e := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show u' x * fderiv ℝ φ x e = u x * fderiv ℝ φ x e
    by_cases hx : x ∈ tsupport φ
    · rw [hu (hφ.2.2 hx)]
    · rw [hfd0 x hx, mul_zero, mul_zero]
  have hR : ∫ x, v' x * φ x = ∫ x, v x * φ x := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show v' x * φ x = v x * φ x
    by_cases hx : x ∈ tsupport φ
    · rw [hv (hφ.2.2 hx)]
    · rw [hφ0 x hx, mul_zero, mul_zero]
  rw [hL, hR]; exact h φ hφ

/-- **Directional derivative of a smooth-left convolution, in scalar form.**  For `ρ` smooth with
compact support and `u` locally integrable, the classical directional derivative of `ρ ⋆ u`
distributes onto `ρ`: `∂ₑ(ρ ⋆ u) = (∂ₑρ) ⋆ u`.  This is Mathlib's
`HasCompactSupport.hasFDerivAt_convolution_left` (which yields the total derivative in the
`precompL` bundled form) evaluated at `e` and pushed through the Bochner integral
(`ContinuousLinearMap.integral_apply` + `precompL_apply`).  It converts the classical gradient of the
mollification into the left-handed scalar convolution `(∂ₑρ)⋆u` that `convolution_deriv_eq_of_subset`
consumes. -/
lemma fderiv_convolution_apply {ρ u : ℝⁿ → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (hρsupp : HasCompactSupport ρ) (hu : LocallyIntegrable u volume) (x e : ℝⁿ) :
    fderiv ℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x e
      = ((fun z => fderiv ℝ ρ z e) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x := by
  set L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ with hLdef
  have hρ1 : ContDiff ℝ 1 ρ := hρ.of_le (by simp)
  have hfd : HasFDerivAt (ρ ⋆[L, volume] u)
      ((fderiv ℝ ρ ⋆[L.precompL ℝⁿ, volume] u) x) x :=
    hρsupp.hasFDerivAt_convolution_left L hρ1 hu x
  have hex : ConvolutionExistsAt (fderiv ℝ ρ) u x (L.precompL ℝⁿ) volume :=
    (hρsupp.fderiv ℝ).convolutionExists_left (L.precompL ℝⁿ)
      (hρ1.continuous_fderiv one_ne_zero) hu x
  rw [hfd.fderiv, convolution_def, ContinuousLinearMap.integral_apply hex]
  simp only [ContinuousLinearMap.precompL_apply]
  rw [convolution_def]

/-- **The inward-shifted mollifier samples only the interior.**  If `ρ`'s support lies in the ball of
radius `r` and the base point `x'` has `i`-th coordinate exceeding `r`, then the reflected bump
`z ↦ ρ(x'−z)` (the kernel of a convolution evaluated at `x'`) is supported entirely inside the open
half-space `{xᵢ>0}`.  This is the geometric heart of the mollification-up-to-the-boundary: after an
inward shift `s > η` the sample point `x' = x + s·eᵢ` has `x'ᵢ ≥ s > η = r`, so the whole convolution
kernel stays in `{xᵢ>0}` where the datum is genuinely Sobolev — the hypothesis
`convolution_deriv_eq_of_subset` and `IsWeakDerivInDir.congr_eqOn` need. -/
lemma tsupport_comp_sub_subset_pos {ρ : ℝⁿ → ℝ} {r : ℝ} {i : Fin n}
    (hρ : tsupport ρ ⊆ Metric.closedBall 0 r) {x' : ℝⁿ} (hx' : r < x' i) :
    tsupport (fun z => ρ (x' - z)) ⊆ {x : ℝⁿ | 0 < x i} := by
  have hcoord : ∀ w : ℝⁿ, |w i| ≤ ‖w‖ := by
    intro w
    rw [EuclideanSpace.norm_eq]
    have hle : ‖w i‖ ≤ Real.sqrt (∑ j, ‖w j‖ ^ 2) := by
      rw [show ‖w i‖ = Real.sqrt (‖w i‖ ^ 2) from (Real.sqrt_sq (norm_nonneg _)).symm]
      exact Real.sqrt_le_sqrt
        (Finset.single_le_sum (fun j _ => sq_nonneg ‖w j‖) (Finset.mem_univ i))
    simpa [Real.norm_eq_abs] using hle
  have hsub : tsupport (fun z => ρ (x' - z)) ⊆ (fun z => x' - z) ⁻¹' (tsupport ρ) := by
    apply closure_minimal
    · intro z hz
      have hz' : x' - z ∈ Function.support ρ := hz
      exact subset_tsupport ρ hz'
    · exact (isClosed_tsupport ρ).preimage (continuous_const.sub continuous_id)
  intro z hz
  have hball : ‖x' - z‖ ≤ r := by
    have := hρ (hsub hz); simpa [Metric.mem_closedBall, dist_eq_norm] using this
  have h1 : |x' i - z i| ≤ r := by
    have h2 : (x' - z) i = x' i - z i := by simp [PiLp.sub_apply]
    have := le_trans (hcoord (x' - z)) hball; rwa [h2] at this
  simp only [Set.mem_setOf_eq]
  have := abs_le.mp h1
  linarith [this.1, this.2]

/-- **Function-part of the boundary density.**  With `ũ = 1_{xᵢ>0}·u` the zero-extension, the
mollified inward-shift `x ↦ (ρ_k ⋆ ũ)(x + s_k·eᵢ)` converges to `u` in `Lᵖ({xᵢ>0})` as the mollifier
radius and shift `→ 0`.  The increment telescopes as `[(ρ_k⋆ũ − ũ)(·+s_k eᵢ)]` (mollification error,
`→0` by the whole-space error `tendsto_eLpNorm_convolution_sub` + translation-invariance of the whole
`Lᵖ` norm) `+ [ũ(·+s_k eᵢ) − u]` (`=ᵐ u(·+s_k eᵢ)−u` on `{xᵢ>0}`, `→0` by
`tendsto_eLpNorm_translate_sub_restrict_pos`). -/
theorem tendsto_eLpNorm_mollify_shift_sub_restrict (i : Fin n) {u : ℝⁿ → ℝ} {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hu : MemLp u p (volume.restrict {x : ℝⁿ | 0 < x i}))
    {φ : ℕ → ContDiffBump (0 : ℝⁿ)} (hφ : Tendsto (fun k => (φ k).rOut) atTop (𝓝 0))
    {s : ℕ → ℝ} (hs0 : ∀ k, 0 < s k) (hs : Tendsto s atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm (fun x =>
      ((φ k).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          Set.indicator {x : ℝⁿ | 0 < x i} u) (x + s k • EuclideanSpace.single i (1 : ℝ))
        - u x) p (volume.restrict {x : ℝⁿ | 0 < x i})) atTop (𝓝 0) := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hmsGt : MeasurableSet {x : ℝⁿ | 0 < x i} :=
    measurableSet_lt measurable_const (EuclideanSpace.proj i).continuous.measurable
  set S : Set ℝⁿ := {x : ℝⁿ | 0 < x i} with hS
  set L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ with hLdef
  set ũ : ℝⁿ → ℝ := S.indicator u with hũdef
  have hũLp : MemLp ũ p volume := (memLp_indicator_iff_restrict hmsGt).2 hu
  have hũLI : LocallyIntegrable ũ volume := hũLp.locallyIntegrable hp1
  set g : ℕ → ℝⁿ → ℝ := fun k => (φ k).normed volume ⋆[L, volume] ũ with hgdef
  have hg_cont : ∀ k, Continuous (g k) := fun k =>
    (φ k).hasCompactSupport_normed.continuous_convolution_left L
      ((φ k).contDiff_normed (n := 1)).continuous hũLI
  have hmem : ∀ {x : ℝⁿ} {t : ℝ}, 0 < x i → 0 < t →
      x + t • EuclideanSpace.single i (1 : ℝ) ∈ S := by
    intro x t hx ht
    have hc : (x + t • EuclideanSpace.single i (1 : ℝ)) i = x i + t := by
      simp [PiLp.add_apply, PiLp.smul_apply]
    simp only [hS, Set.mem_setOf_eq, hc]; linarith
  -- aesm helpers (w.r.t. `volume.restrict S`)
  have haesm_g : ∀ (k : ℕ) (t : ℝ), AEStronglyMeasurable (fun x =>
      g k (x + t • EuclideanSpace.single i (1 : ℝ))) (volume.restrict S) := fun k t =>
    ((hg_cont k).comp (continuous_id.add continuous_const)).aestronglyMeasurable.restrict
  have haesm_ũ : ∀ (t : ℝ), AEStronglyMeasurable (fun x =>
      ũ (x + t • EuclideanSpace.single i (1 : ℝ))) (volume.restrict S) := fun t =>
    (hũLp.aestronglyMeasurable.comp_quasiMeasurePreserving
      (measurePreserving_add_right volume _).quasiMeasurePreserving).restrict
  have haesm_u : AEStronglyMeasurable u (volume.restrict S) := hu.aestronglyMeasurable
  set A : ℕ → ℝ≥0∞ := fun k => eLpNorm (fun x =>
      g k (x + s k • EuclideanSpace.single i (1 : ℝ))
        - ũ (x + s k • EuclideanSpace.single i (1 : ℝ))) p (volume.restrict S) with hAdef
  set B : ℕ → ℝ≥0∞ := fun k => eLpNorm (fun x =>
      ũ (x + s k • EuclideanSpace.single i (1 : ℝ)) - u x) p (volume.restrict S) with hBdef
  have hA : Tendsto A atTop (𝓝 0) := by
    have hconv : Tendsto (fun k => eLpNorm (fun x => g k x - ũ x) p volume) atTop (𝓝 0) :=
      tendsto_eLpNorm_convolution_sub hp hũLp hφ
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hconv
      (Eventually.of_forall fun k => zero_le _) (Eventually.of_forall fun k => ?_)
    have haesm : AEStronglyMeasurable (fun x => g k x - ũ x) volume :=
      (hg_cont k).aestronglyMeasurable.sub hũLp.aestronglyMeasurable
    have htrans : eLpNorm (fun x => g k (x + s k • EuclideanSpace.single i (1 : ℝ))
          - ũ (x + s k • EuclideanSpace.single i (1 : ℝ))) p volume
        = eLpNorm (fun x => g k x - ũ x) p volume := by
      have := eLpNorm_comp_measurePreserving (p := p) (g := fun x => g k x - ũ x)
        haesm (measurePreserving_add_right volume (s k • EuclideanSpace.single i (1 : ℝ)))
      simpa [Function.comp] using this
    calc A k ≤ eLpNorm (fun x => g k (x + s k • EuclideanSpace.single i (1 : ℝ))
              - ũ (x + s k • EuclideanSpace.single i (1 : ℝ))) p volume :=
            eLpNorm_mono_measure _ Measure.restrict_le_self
      _ = eLpNorm (fun x => g k x - ũ x) p volume := htrans
  have hB : Tendsto B atTop (𝓝 0) := by
    have hBeq : B = fun k => eLpNorm (fun x =>
        u (x + s k • EuclideanSpace.single i (1 : ℝ)) - u x) p (volume.restrict S) := by
      funext k
      refine eLpNorm_congr_ae ((ae_restrict_iff' hmsGt).2 (Eventually.of_forall
        (fun x (hx : 0 < x i) => ?_)))
      show ũ (x + s k • EuclideanSpace.single i (1 : ℝ)) - u x
          = u (x + s k • EuclideanSpace.single i (1 : ℝ)) - u x
      rw [hũdef, Set.indicator_of_mem (hmem hx (hs0 k))]
    rw [hBeq]
    exact (tendsto_eLpNorm_translate_sub_restrict_pos i hp hu).comp
      (tendsto_nhdsWithin_iff.mpr ⟨hs, Eventually.of_forall hs0⟩)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa using hA.add hB) (Eventually.of_forall fun k => zero_le _)
    (Eventually.of_forall fun k => ?_)
  have hsplit : (fun x => g k (x + s k • EuclideanSpace.single i (1 : ℝ)) - u x)
      = (fun x => g k (x + s k • EuclideanSpace.single i (1 : ℝ))
            - ũ (x + s k • EuclideanSpace.single i (1 : ℝ)))
        + (fun x => ũ (x + s k • EuclideanSpace.single i (1 : ℝ)) - u x) := by
    funext x; simp only [Pi.add_apply]; ring
  rw [hsplit]
  exact eLpNorm_add_le ((haesm_g k (s k)).sub (haesm_ũ (s k)))
    ((haesm_ũ (s k)).sub haesm_u) hp1

/-- **Gradient identity for the mollified inward-shift.**  On the interior `{xᵢ>0}`, the classical
directional derivative of `y ↦ (ρ ⋆ ũ)(y + t·eᵢ)` (with `ũ = 1_{xᵢ>0}·u`) equals `(ρ ⋆ ṽⱼ)(·+t·eᵢ)`
with `ṽⱼ = 1_{xᵢ>0}·vⱼ` the zero-extension of the weak derivative.  Chains the chain rule,
`fderiv_convolution_apply` (`∂ⱼ(ρ⋆ũ) = (∂ⱼρ)⋆ũ`), and `convolution_deriv_eq_of_subset`
(`(∂ⱼρ)⋆ũ = ρ⋆ṽⱼ` since the inward shift `t > ψ.rOut` keeps the kernel support inside `{xᵢ>0}`, where
`ũ`, `ṽⱼ` carry `u`'s weak derivative by `congr_eqOn`).  This makes the gradient-part of the density
a corollary of the function-part applied to `vⱼ`. -/
lemma fderiv_mollify_shift_apply_of_pos (i j : Fin n) {u vj : ℝⁿ → ℝ}
    (hweak : IsWeakDerivInDir {x : ℝⁿ | 0 < x i} (EuclideanSpace.single j (1 : ℝ)) u vj)
    (huLI : LocallyIntegrable (Set.indicator {x : ℝⁿ | 0 < x i} u) volume)
    (ψ : ContDiffBump (0 : ℝⁿ)) {t : ℝ} (ht : ψ.rOut < t) {x : ℝⁿ} (hx : 0 < x i) :
    fderiv ℝ (fun y => (ψ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        Set.indicator {x : ℝⁿ | 0 < x i} u) (y + t • EuclideanSpace.single i (1 : ℝ)))
        x (EuclideanSpace.single j (1 : ℝ))
      = (ψ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          Set.indicator {x : ℝⁿ | 0 < x i} vj) (x + t • EuclideanSpace.single i (1 : ℝ)) := by
  set S : Set ℝⁿ := {x : ℝⁿ | 0 < x i} with hS
  set ρ : ℝⁿ → ℝ := ψ.normed volume with hρdef
  set c : ℝⁿ := t • EuclideanSpace.single i (1 : ℝ) with hcdef
  have hρcd : ContDiff ℝ ∞ ρ := ψ.contDiff_normed
  have hρsupp : HasCompactSupport ρ := ψ.hasCompactSupport_normed
  have hgcd : ContDiff ℝ ∞ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] S.indicator u) :=
    hρsupp.contDiff_convolution_left _ hρcd huLI
  have hchain : fderiv ℝ (fun y => (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] S.indicator u) (y + c))
        x (EuclideanSpace.single j (1 : ℝ))
      = fderiv ℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] S.indicator u) (x + c)
        (EuclideanSpace.single j (1 : ℝ)) := by
    have h1 : HasFDerivAt (fun y : ℝⁿ => y + c) (ContinuousLinearMap.id ℝ ℝⁿ) x := by
      simpa using (hasFDerivAt_id x).add_const c
    have h2 : HasFDerivAt (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] S.indicator u)
        (fderiv ℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] S.indicator u) (x + c)) (x + c) :=
      (hgcd.differentiable (by simp)).differentiableAt.hasFDerivAt
    have hcomp : HasFDerivAt
        (fun y => (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] S.indicator u) (y + c))
        (fderiv ℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] S.indicator u) (x + c)) x := by
      simpa [Function.comp_def] using h2.comp x h1
    rw [hcomp.fderiv]
  rw [hchain, fderiv_convolution_apply hρcd hρsupp huLI]
  refine convolution_deriv_eq_of_subset (U := S) hρcd hρsupp (EuclideanSpace.single j (1 : ℝ))
    ?_ (x + c) ?_
  · exact hweak.congr_eqOn (fun y hy => Set.indicator_of_mem hy u)
      (fun y hy => Set.indicator_of_mem hy vj)
  · refine tsupport_comp_sub_subset_pos (r := ψ.rOut) ?_ ?_
    · rw [hρdef, tsupport, ψ.support_normed_eq]
      exact closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall
    · have hc : (x + c) i = x i + t := by rw [hcdef]; simp [PiLp.add_apply, PiLp.smul_apply]
      rw [hc]; linarith

/-- **`Lᵖ`-membership of a mollification.**  For a mollifier `η` (smooth, compact support, nonneg,
`∫η = 1`) and `f ∈ Lᵖ(ℝⁿ)`, the convolution `η ⋆ f` lies in `Lᵖ`.  Mathlib has no convolution Young
inequality, so this is obtained by triangle inequality from the project's own convolution-error bound:
`MemLp(η⋆f) = MemLp((η⋆f − f) + f)`, and `η⋆f − f ∈ Lᵖ` because `eLpNorm_convolution_sub_rpow_le`
bounds its `p`-th power by `∫η(y)·‖f(·−y)−f‖ₚ^p ≤ (2‖f‖ₚ)^p < ∞`. -/
theorem memLp_convolution {η : ℝⁿ → ℝ} (hη_cd : ContDiff ℝ ∞ η) (hη_supp : HasCompactSupport η)
    (hη_nonneg : ∀ y, 0 ≤ η y) (hη_int : ∫ y, η y = 1) {u : ℝⁿ → ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hu : MemLp u p volume) :
    MemLp (η ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) p volume := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hP0 : 0 < p.toReal := by
    have h0 : (0 : ℝ) < (1 : ℝ≥0∞).toReal := by simp
    exact h0.trans_le (ENNReal.toReal_mono hp hp1)
  have hη_cont : Continuous η := hη_cd.continuous
  have hu_li : LocallyIntegrable u volume := hu.locallyIntegrable hp1
  have hcont : Continuous (η ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) :=
    hη_supp.continuous_convolution_left _ hη_cont hu_li
  have hw_meas : AEMeasurable (fun y => ENNReal.ofReal (η y)) volume :=
    (ENNReal.measurable_ofReal.comp hη_cont.measurable).aemeasurable
  have hw1 : ∫⁻ y, ENNReal.ofReal (η y) ∂volume = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hη_cont.integrable_of_hasCompactSupport hη_supp)
      (Filter.Eventually.of_forall hη_nonneg), hη_int, ENNReal.ofReal_one]
  have hCle : ∀ y : ℝⁿ, eLpNorm (fun x => u (x - y) - u x) p volume ≤ 2 * eLpNorm u p volume := by
    intro y
    have hmp : MeasurePreserving (fun x : ℝⁿ => x - y) volume volume :=
      measurePreserving_sub_right volume y
    have h1 : eLpNorm (fun x => u (x - y)) p volume = eLpNorm u p volume :=
      eLpNorm_comp_measurePreserving hu.aestronglyMeasurable hmp
    calc eLpNorm (fun x => u (x - y) - u x) p volume
        ≤ eLpNorm (fun x => u (x - y)) p volume + eLpNorm u p volume :=
          eLpNorm_sub_le (hu.aestronglyMeasurable.comp_measurePreserving hmp)
            hu.aestronglyMeasurable hp1
      _ = 2 * eLpNorm u p volume := by rw [h1, two_mul]
  have hCfin : (2 * eLpNorm u p volume) ^ p.toReal ≠ ⊤ :=
    (ENNReal.rpow_lt_top_of_nonneg hP0.le
      (ENNReal.mul_lt_top (by norm_num) hu.2).ne).ne
  have hfin : eLpNorm (fun x => (η ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x - u x) p volume
      < ⊤ := by
    have hkey := eLpNorm_convolution_sub_rpow_le hη_cont hη_supp hη_nonneg hη_int hp hu
    have hRHS : ∫⁻ y, ENNReal.ofReal (η y)
          * (eLpNorm (fun x => u (x - y) - u x) p volume) ^ p.toReal ∂volume
        ≤ (2 * eLpNorm u p volume) ^ p.toReal := by
      calc ∫⁻ y, ENNReal.ofReal (η y)
            * (eLpNorm (fun x => u (x - y) - u x) p volume) ^ p.toReal ∂volume
          ≤ ∫⁻ _y, ENNReal.ofReal (η _y) * (2 * eLpNorm u p volume) ^ p.toReal ∂volume := by
            refine lintegral_mono fun y => ?_
            gcongr
            exact hCle y
        _ = (2 * eLpNorm u p volume) ^ p.toReal * ∫⁻ y, ENNReal.ofReal (η y) ∂volume := by
            simp_rw [mul_comm (ENNReal.ofReal _)]
            rw [lintegral_const_mul'' _ hw_meas]
        _ = (2 * eLpNorm u p volume) ^ p.toReal := by rw [hw1, mul_one]
    have hlt : (eLpNorm (fun x => (η ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x - u x) p volume)
        ^ p.toReal < ⊤ := lt_of_le_of_lt (hkey.trans hRHS) hCfin.lt_top
    by_contra htop
    rw [not_lt, top_le_iff] at htop
    rw [htop, ENNReal.top_rpow_of_pos hP0] at hlt
    exact lt_irrefl _ hlt
  have hsub : MemLp (fun x => (η ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x - u x) p volume :=
    ⟨hcont.aestronglyMeasurable.sub hu.aestronglyMeasurable, hfin⟩
  have heq : (η ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u)
      = fun x => ((η ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x - u x) + u x := by
    funext x; ring
  rw [heq]
  exact hsub.add hu

/-- **Boundary density for the half-space (sequence form).**  A `W^{1,p}(\{xᵢ>0\})` function `u` with
weak derivatives `v` is approximated in `W^{1,p}(\{xᵢ>0\})` by a sequence of `C^∞` functions
`wₖ = (ρ_k ⋆ ũ)(·+sₖ·eᵢ)` (mollified inward-shifts, `ũ = 1_{xᵢ>0}·u`): both `‖u−wₖ‖_{Lᵖ} → 0` and,
for every `j`, `‖vⱼ − ∂ⱼwₖ‖_{Lᵖ} → 0`.  Assembles the function-part
(`tendsto_eLpNorm_mollify_shift_sub_restrict`) with the gradient identity
(`fderiv_mollify_shift_apply_of_pos`, which turns the gradient-part into the function-part applied to
`vⱼ`), over the concrete family `rInₖ=1/(k+3)`, `rOutₖ=1/(k+2)`, `sₖ=1/(k+1)`. -/
theorem exists_seq_contDiff_tendsto_halfspace (i : Fin n) {u : ℝⁿ → ℝ} {v : Fin n → ℝⁿ → ℝ}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (hu : MemLp u p (volume.restrict {x : ℝⁿ | 0 < x i}))
    (hv : ∀ j, MemLp (v j) p (volume.restrict {x : ℝⁿ | 0 < x i}))
    (hweak : ∀ j, IsWeakDerivInDir {x : ℝⁿ | 0 < x i} (EuclideanSpace.single j (1 : ℝ)) u (v j)) :
    ∃ w : ℕ → ℝⁿ → ℝ, (∀ k, ContDiff ℝ ∞ (w k)) ∧
      Tendsto (fun k => eLpNorm (fun x => w k x - u x) p (volume.restrict {x : ℝⁿ | 0 < x i}))
        atTop (𝓝 0) ∧
      (∀ j, Tendsto (fun k => eLpNorm
          (fun x => fderiv ℝ (w k) x (EuclideanSpace.single j (1 : ℝ)) - v j x) p
          (volume.restrict {x : ℝⁿ | 0 < x i})) atTop (𝓝 0)) ∧
      (∀ k, MemLp (w k) p (volume.restrict {x : ℝⁿ | 0 < x i})) ∧
      (∀ j k, MemLp (fun x => fderiv ℝ (w k) x (EuclideanSpace.single j (1 : ℝ))) p
        (volume.restrict {x : ℝⁿ | 0 < x i})) := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hmsGt : MeasurableSet {x : ℝⁿ | 0 < x i} :=
    measurableSet_lt measurable_const (EuclideanSpace.proj i).continuous.measurable
  have hũLp : MemLp (Set.indicator {x : ℝⁿ | 0 < x i} u) p volume :=
    (memLp_indicator_iff_restrict hmsGt).2 hu
  have huLI : LocallyIntegrable (Set.indicator {x : ℝⁿ | 0 < x i} u) volume :=
    hũLp.locallyIntegrable hp1
  have htend : ∀ c : ℝ, Tendsto (fun k : ℕ => 1 / ((k : ℝ) + c)) atTop (𝓝 0) := by
    intro c
    have h1 : Tendsto (fun k : ℕ => (k : ℝ) + c) atTop atTop :=
      tendsto_atTop_add_const_right _ c tendsto_natCast_atTop_atTop
    simpa [one_div] using h1.inv_tendsto_atTop
  set ψ : ℕ → ContDiffBump (0 : ℝⁿ) := fun k =>
    { rIn := 1 / ((k : ℝ) + 3), rOut := 1 / ((k : ℝ) + 2), rIn_pos := by positivity,
      rIn_lt_rOut := one_div_lt_one_div_of_lt (by positivity) (by linarith) } with hψ
  set sq : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) with hsq
  have hφ : Tendsto (fun k => (ψ k).rOut) atTop (𝓝 0) := by simpa [hψ] using htend 2
  have hs0 : ∀ k, 0 < sq k := fun k => by rw [hsq]; positivity
  have hs : Tendsto sq atTop (𝓝 0) := by simpa [hsq] using htend 1
  have hrs : ∀ k, (ψ k).rOut < sq k := fun k => by
    show (1 : ℝ) / ((k : ℝ) + 2) < 1 / ((k : ℝ) + 1)
    exact one_div_lt_one_div_of_lt (by positivity) (by linarith)
  refine ⟨fun k x => ((ψ k).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      Set.indicator {x : ℝⁿ | 0 < x i} u) (x + sq k • EuclideanSpace.single i (1 : ℝ)),
    ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    exact ((ψ k).hasCompactSupport_normed.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
      (ψ k).contDiff_normed huLI).comp (contDiff_id.add contDiff_const)
  · exact tendsto_eLpNorm_mollify_shift_sub_restrict i hp hu hφ hs0 hs
  · intro j
    refine (tendsto_eLpNorm_mollify_shift_sub_restrict i hp (hv j) hφ hs0 hs).congr (fun k => ?_)
    refine eLpNorm_congr_ae ((ae_restrict_iff' hmsGt).2 (Filter.Eventually.of_forall
      fun x (hx : 0 < x i) => ?_))
    show ((ψ k).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          Set.indicator {x : ℝⁿ | 0 < x i} (v j))
          (x + sq k • EuclideanSpace.single i (1 : ℝ)) - v j x
      = fderiv ℝ (fun y => ((ψ k).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          Set.indicator {x : ℝⁿ | 0 < x i} u) (y + sq k • EuclideanSpace.single i (1 : ℝ))) x
          (EuclideanSpace.single j (1 : ℝ)) - v j x
    rw [fderiv_mollify_shift_apply_of_pos i j (hweak j) huLI (ψ k) (hrs k) hx]
  · -- `MemLp (w k)` on `{xᵢ>0}`
    intro k
    have hconv : MemLp ((ψ k).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        Set.indicator {x : ℝⁿ | 0 < x i} u) p volume :=
      memLp_convolution (ψ k).contDiff_normed (ψ k).hasCompactSupport_normed
        (ψ k).nonneg_normed (ψ k).integral_normed hp hũLp
    exact (hconv.comp_measurePreserving
      (measurePreserving_add_right volume (sq k • EuclideanSpace.single i (1 : ℝ)))).restrict _
  · -- `MemLp (∂ⱼ(w k))` on `{xᵢ>0}`, via the gradient identity
    intro j k
    have hvjLp : MemLp (Set.indicator {x : ℝⁿ | 0 < x i} (v j)) p volume :=
      (memLp_indicator_iff_restrict hmsGt).2 (hv j)
    have hconvv : MemLp ((ψ k).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        Set.indicator {x : ℝⁿ | 0 < x i} (v j)) p volume :=
      memLp_convolution (ψ k).contDiff_normed (ψ k).hasCompactSupport_normed
        (ψ k).nonneg_normed (ψ k).integral_normed hp hvjLp
    have hRHS : MemLp (fun x => ((ψ k).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          Set.indicator {x : ℝⁿ | 0 < x i} (v j)) (x + sq k • EuclideanSpace.single i (1 : ℝ))) p
        (volume.restrict {x : ℝⁿ | 0 < x i}) :=
      (hconvv.comp_measurePreserving
        (measurePreserving_add_right volume (sq k • EuclideanSpace.single i (1 : ℝ)))).restrict _
    have hae : (fun x => fderiv ℝ (fun y => ((ψ k).normed volume
            ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] Set.indicator {x : ℝⁿ | 0 < x i} u)
            (y + sq k • EuclideanSpace.single i (1 : ℝ))) x (EuclideanSpace.single j (1 : ℝ)))
        =ᵐ[volume.restrict {x : ℝⁿ | 0 < x i}]
          (fun x => ((ψ k).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
            Set.indicator {x : ℝⁿ | 0 < x i} (v j)) (x + sq k • EuclideanSpace.single i (1 : ℝ))) := by
      refine (ae_restrict_iff' hmsGt).2 (Filter.Eventually.of_forall (fun x (hx : 0 < x i) => ?_))
      exact fderiv_mollify_shift_apply_of_pos i j (hweak j) huLI (ψ k) (hrs k) hx
    exact (memLp_congr_ae hae).mpr hRHS

/-- **Restricted `Lᵖ` bound for a normal-glue-shaped function.**  Companion of
`eLpNorm_normalGlue_le` with the right-hand side measured only on the upper half-space `{xᵢ≥0}`,
provided the lower branch `B` (on `{xᵢ≤0}`) is dominated there by `g` on `{xᵢ≥0}`.  The `{xᵢ<0}`
values of `g` never enter — exactly what the bounded-extension-by-density argument requires. -/
theorem eLpNorm_normalGlue_le_restrict (i : Fin n) {p : ℝ≥0∞} (hp : 1 ≤ p) {g B : ℝⁿ → ℝ}
    (hg : AEStronglyMeasurable g volume) (hB : AEStronglyMeasurable B volume)
    (hBg : eLpNorm B p (volume.restrict {x : ℝⁿ | x i ≤ 0})
      ≤ eLpNorm g p (volume.restrict {x : ℝⁿ | 0 ≤ x i})) :
    eLpNorm (fun x => if 0 < x i then g x else B x) p volume
      ≤ 2 * eLpNorm g p (volume.restrict {x : ℝⁿ | 0 ≤ x i}) := by
  have hmsGt : MeasurableSet {x : ℝⁿ | 0 < x i} :=
    measurableSet_lt measurable_const (EuclideanSpace.proj i).continuous.measurable
  have hmsLe : MeasurableSet {x : ℝⁿ | x i ≤ 0} :=
    measurableSet_le (EuclideanSpace.proj i).continuous.measurable measurable_const
  have heqv : (fun x => if 0 < x i then g x else B x)
      = fun x => {x : ℝⁿ | 0 < x i}.indicator g x + {x : ℝⁿ | x i ≤ 0}.indicator B x := by
    funext x
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    by_cases hx : 0 < x i
    · rw [if_pos hx, if_pos hx, if_neg (not_le.2 hx), add_zero]
    · rw [if_neg hx, if_neg hx, if_pos (not_lt.1 hx), zero_add]
  rw [heqv]
  calc eLpNorm (fun x => {x : ℝⁿ | 0 < x i}.indicator g x
          + {x : ℝⁿ | x i ≤ 0}.indicator B x) p volume
      ≤ eLpNorm ({x : ℝⁿ | 0 < x i}.indicator g) p volume
        + eLpNorm ({x : ℝⁿ | x i ≤ 0}.indicator B) p volume :=
        eLpNorm_add_le (hg.indicator hmsGt) (hB.indicator hmsLe) hp
    _ = eLpNorm g p (volume.restrict {x : ℝⁿ | 0 < x i})
        + eLpNorm B p (volume.restrict {x : ℝⁿ | x i ≤ 0}) := by
        rw [eLpNorm_indicator_eq_eLpNorm_restrict hmsGt,
          eLpNorm_indicator_eq_eLpNorm_restrict hmsLe]
    _ ≤ eLpNorm g p (volume.restrict {x : ℝⁿ | 0 ≤ x i})
        + eLpNorm g p (volume.restrict {x : ℝⁿ | 0 ≤ x i}) :=
        add_le_add (eLpNorm_mono_measure g
          (Measure.restrict_mono (Set.setOf_subset_setOf.2 (fun _ hx => hx.le)) le_rfl)) hBg
    _ = 2 * eLpNorm g p (volume.restrict {x : ℝⁿ | 0 ≤ x i}) := (two_mul _).symm

/-- **Restricted `Lᵖ` bound for the even reflection's weak gradient.**  As `eLpNorm_evenRefl_grad_le`
but measuring `∂ⱼu` only on `{xᵢ≥0}`: the reflected `eⱼ`-derivative of `evenRefl i u` has `Lᵖ` norm
`≤ 2‖∂ⱼu‖_{Lᵖ(\{xᵢ≥0\})}`.  The lower branch `(±1)·∂ⱼu∘refll` on `{xᵢ≤0}` is pushed to `∂ⱼu` on
`{xᵢ≥0}` by the measure-preserving `refll : \{xᵢ≤0\}→\{xᵢ≥0\}`. -/
theorem eLpNorm_evenRefl_grad_le_restrict (i j : Fin n) {u : ℝⁿ → ℝ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hg : AEStronglyMeasurable
      (fun x => fderiv ℝ u x (EuclideanSpace.single j (1 : ℝ))) volume) :
    eLpNorm (fun x => if 0 < x i then fderiv ℝ u x (EuclideanSpace.single j (1 : ℝ))
        else (if j = i then (-1 : ℝ) else 1)
          * fderiv ℝ u (refll i x) (EuclideanSpace.single j (1 : ℝ))) p volume
      ≤ 2 * eLpNorm (fun x => fderiv ℝ u x (EuclideanSpace.single j (1 : ℝ))) p
        (volume.restrict {x : ℝⁿ | 0 ≤ x i}) := by
  have hmsGe : MeasurableSet {x : ℝⁿ | 0 ≤ x i} :=
    measurableSet_le measurable_const (EuclideanSpace.proj i).continuous.measurable
  have hB : AEStronglyMeasurable (fun x => (if j = i then (-1 : ℝ) else 1)
      * fderiv ℝ u (refll i x) (EuclideanSpace.single j (1 : ℝ))) volume :=
    (hg.comp_measurePreserving (refll_measurePreserving i)).const_mul _
  have hpre : refll i ⁻¹' {x : ℝⁿ | 0 ≤ x i} = {x : ℝⁿ | x i ≤ 0} := by
    ext x; simp only [Set.mem_preimage, Set.mem_setOf_eq, refll_apply_self]; constructor <;> intro h <;>
      linarith
  have hmp : MeasurePreserving (refll i) (volume.restrict {x : ℝⁿ | x i ≤ 0})
      (volume.restrict {x : ℝⁿ | 0 ≤ x i}) := by
    have h := (refll_measurePreserving i).restrict_preimage hmsGe
    rwa [hpre] at h
  have hBg : eLpNorm (fun x => (if j = i then (-1 : ℝ) else 1)
        * fderiv ℝ u (refll i x) (EuclideanSpace.single j (1 : ℝ))) p
        (volume.restrict {x : ℝⁿ | x i ≤ 0})
      ≤ eLpNorm (fun x => fderiv ℝ u x (EuclideanSpace.single j (1 : ℝ))) p
        (volume.restrict {x : ℝⁿ | 0 ≤ x i}) := by
    have hfun : (fun x => (if j = i then (-1 : ℝ) else 1)
          * fderiv ℝ u (refll i x) (EuclideanSpace.single j (1 : ℝ)))
        = (fun y => (if j = i then (-1 : ℝ) else 1)
          * fderiv ℝ u y (EuclideanSpace.single j (1 : ℝ))) ∘ refll i := rfl
    rw [hfun, eLpNorm_comp_measurePreserving
      ((hg.mono_measure Measure.restrict_le_self).const_mul _) hmp]
    split_ifs with h
    · simp only [neg_one_mul]
      exact le_of_eq (eLpNorm_neg (fun y => fderiv ℝ u y (EuclideanSpace.single j (1 : ℝ))) p
        (volume.restrict {x : ℝⁿ | 0 ≤ x i}))
    · simp only [one_mul, le_refl]
  exact eLpNorm_normalGlue_le_restrict i hp hg hB hBg



end Sobolev

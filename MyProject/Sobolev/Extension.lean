import MyProject.Sobolev.Basic

/-!
# Sobolev extension operator (Evans §5.4) — foundations

The extension theorem builds a bounded linear operator `E : W^{1,p}(Ω) → W^{1,p}(ℝⁿ)` extending
functions off a bounded `C¹` domain, by reflecting across a (locally flattened) boundary.  This file
begins with the local engine: the **reflection across the coordinate hyperplane `{xᵢ = 0}`**,
packaged as a linear isometry equivalence so that smoothness, involutivity and measure-preservation
are all available for the reflection-extension estimate that follows.
-/

open MeasureTheory Filter
open scoped RealInnerProductSpace ContDiff Topology ENNReal

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


end Sobolev

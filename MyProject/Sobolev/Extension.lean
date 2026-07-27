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
open scoped RealInnerProductSpace ContDiff Topology

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


end Sobolev

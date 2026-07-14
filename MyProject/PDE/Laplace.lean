import MyProject.Common.AreaFormula

/-! ## Gauss–Green corollaries for the Laplace equation

The following block (sphere surface measure, Green's identities, and the mean-value property) is
built on the general divergence theorem from `AreaFormula`; it is placed here as it belongs to the
Laplace chapter (Evans §2.2). It stays in the `AreaFormula` namespace and dimension `m+2`. -/

namespace AreaFormula

open MeasureTheory MeasureTheory.Measure Matrix Module Filter Topology Metric Set Asymptotics
open InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Pointwise Manifold

noncomputable section

local notation "ℝ^" m => EuclideanSpace ℝ (Fin m)

variable {m : ℕ}

/-! ### Sphere surface measure

Applying the divergence theorem to the identity field `F(y) = y - c` on the ball reads off the
sphere's surface measure from the ball's volume: `divergenceE F ≡ m+2` (trace of the identity),
while `⟪F, ν⟫ ≡ r` on the sphere, so `(m+2)·vol(B) = r·σ(∂B)`. -/

/-- **Sphere surface measure (core identity).** Applying the divergence theorem to the identity
field `F(y) = y - c` on the ball relates the sphere's surface measure to the ball's volume:
`(m+2)·vol(B) = r·σ(∂B)`. -/
theorem sphere_surfaceMeasure_aux (c : ℝ^(m + 2)) (r : ℝ) (hr : 0 < r) :
    (volume (Metric.ball c r)).toReal * (m + 2)
      = (μHE[m + 1] (Metric.sphere c r)).toReal * r := by
  have hΩ := isBoundedC1Domain_ball c r hr
  have hν := isOutwardNormal_ball c r hr
  have hF : ContDiff ℝ 1 (fun y : ℝ^(m + 2) => y - c) := contDiff_id.sub contDiff_const
  have hdt := divergence_theorem hΩ hν hF
  -- LHS: divergenceE of the identity field is the dimension `m + 2`
  have hdiv : ∀ x : ℝ^(m + 2), divergenceE (fun y => y - c) x = (m + 2 : ℝ) := by
    intro x
    have hfd : fderiv ℝ (fun y : ℝ^(m + 2) => y - c) x = ContinuousLinearMap.id ℝ (ℝ^(m + 2)) :=
      ((hasFDerivAt_id x).sub_const c).fderiv
    rw [divergenceE_eq_trace, hfd, ContinuousLinearMap.coe_id, LinearMap.trace_id,
      finrank_euclideanSpace_fin]
    push_cast; ring
  simp only [hdiv] at hdt
  rw [setIntegral_const] at hdt
  -- RHS: the flux integrand is constant `r` on the sphere
  rw [frontier_ball c hr.ne'] at hdt
  have hint : ∀ x ∈ Metric.sphere c r, (⟪x - c, r⁻¹ • (x - c)⟫ : ℝ) = r := by
    intro x hx
    rw [real_inner_smul_right, real_inner_self_eq_norm_mul_norm]
    have hnorm : ‖x - c‖ = r := by rw [← dist_eq_norm]; exact Metric.mem_sphere.mp hx
    rw [hnorm, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]
  rw [setIntegral_congr_fun isClosed_sphere.measurableSet hint, setIntegral_const] at hdt
  simp only [smul_eq_mul, measureReal_def] at hdt
  exact hdt

/-- **Sphere surface measure.** The `(m+1)`-dimensional surface measure of the sphere `∂B(c,r)` in
`ℝ^{m+2}` equals `(m+2)·vol(B(c,r))/r`; combined with `vol(B) = ωₙ rⁿ` this is `n·ωₙ·rⁿ⁻¹`. -/
theorem sphere_surfaceMeasure (c : ℝ^(m + 2)) (r : ℝ) (hr : 0 < r) :
    (μHE[m + 1] (Metric.sphere c r)).toReal
      = (m + 2) * (volume (Metric.ball c r)).toReal / r := by
  rw [eq_div_iff hr.ne']
  linarith [sphere_surfaceMeasure_aux c r hr,
    mul_comm ((m : ℝ) + 2) (volume (Metric.ball c r)).toReal]


/-! ### Divergence of the gradient is the Laplacian

`divergenceE (gradient f)` equals Mathlib's `Laplacian.laplacian f`, connecting the canonical flat
divergence used by the Gauss–Green theorem to the PDE Laplacian (and hence to `IsHarmonic`). Both
sides reduce to the trace of the Hessian: `divergenceE (∇f) x = ∑ᵢ ∂ᵢ(∇f)ᵢ`, and via the coordinate
formula `(∇f)ⱼ = fderiv f eⱼ` each summand is `fderiv² f x eᵢ eᵢ = iteratedFDeriv 2 f x ![eᵢ, eᵢ]`,
which sums to the Laplacian in the `basisFun` orthonormal basis. -/

/-- The real inner product of two scalars is their product (bridging the real-inner diamond). -/
private lemma real_inner_scalars (a b : ℝ) : (⟪a, b⟫ : ℝ) = a * b :=
  (Real.ext_cauchy rfl).trans (mul_comm b a)

open InnerProductSpace in
/-- **Divergence of the gradient is the Laplacian.** The canonical flat divergence of `gradient f`
equals the standard Laplacian `Δf`, connecting `divergenceE` to the PDE Laplacian. -/
lemma divergenceE_gradient_eq_laplacian {n : ℕ} (f : (ℝ^n) → ℝ) (hf : ContDiff ℝ 2 f) (x : ℝ^n) :
    divergenceE (gradient f) x = Laplacian.laplacian f x := by
  have hfdiff : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hfd1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hfd2 : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) x :=
    (hfd1.differentiable (by norm_num)).differentiableAt.hasFDerivAt
  -- coordinate extraction `w j = ⟪single j 1, w⟫`
  have hInnerCoord : ∀ (w : ℝ^n) (j : Fin n), w.ofLp j = ⟪EuclideanSpace.single j (1:ℝ), w⟫ := by
    intro w j
    rw [PiLp.inner_apply]
    simp [real_inner_scalars]
  -- coordinate formula `(∇f y) j = fderiv f y eⱼ`
  have hcoord : ∀ (y : ℝ^n) (j : Fin n),
      (gradient f y).ofLp j = fderiv ℝ f y (EuclideanSpace.single j 1) := by
    intro y j
    rw [hInnerCoord, real_inner_comm]
    exact inner_gradient_left (hfdiff y)
  have hcoordfun : ∀ i : Fin n, (fun y => (gradient f y).ofLp i)
      = fun y => fderiv ℝ f y (EuclideanSpace.single i 1) := fun i => funext (fun y => hcoord y i)
  -- `∇f` is `C¹`, hence differentiable
  have hgrad_cd : ContDiff ℝ 1 (gradient f) := by
    rw [contDiff_euclidean]
    intro i
    rw [hcoordfun i]
    exact (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i 1)).contDiff.comp hfd1
  have hgrad_fd : HasFDerivAt (gradient f) (fderiv ℝ (gradient f) x) x :=
    (hgrad_cd.differentiable (by norm_num)).differentiableAt.hasFDerivAt
  rw [divergenceE, show Laplacian.laplacian f x = ∑ i, iteratedFDeriv ℝ 2 f x
      ![EuclideanSpace.basisFun (Fin n) ℝ i, EuclideanSpace.basisFun (Fin n) ℝ i] from
    congr_fun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f
      (EuclideanSpace.basisFun (Fin n) ℝ)) x]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [EuclideanSpace.basisFun_apply, iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  -- coordinate-of-derivative = derivative-of-coordinate (via `innerSL`)
  have h1 : HasFDerivAt (fun y => (gradient f y).ofLp i)
      ((innerSL ℝ (EuclideanSpace.single i (1:ℝ))).comp (fderiv ℝ (gradient f) x)) x := by
    refine ((innerSL ℝ (EuclideanSpace.single i (1:ℝ))).hasFDerivAt.comp x
      hgrad_fd).congr_of_eventuallyEq (Filter.Eventually.of_forall (fun y => ?_))
    rw [Function.comp_apply, innerSL_apply_apply, ← hInnerCoord]
  have hG : HasFDerivAt (fun y => fderiv ℝ f y (EuclideanSpace.single i 1))
      ((ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i 1)).comp
        (fderiv ℝ (fderiv ℝ f) x)) x :=
    ((ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i 1)).hasFDerivAt.comp x
      hfd2).congr_of_eventuallyEq (Filter.Eventually.of_forall (fun y => rfl))
  have e1 : ((fderiv ℝ (gradient f) x) (EuclideanSpace.single i 1)).ofLp i
      = fderiv ℝ (fun y => (gradient f y).ofLp i) x (EuclideanSpace.single i 1) := by
    rw [h1.fderiv, ContinuousLinearMap.comp_apply, innerSL_apply_apply, ← hInnerCoord]
  rw [e1, hcoordfun i, hG.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]


/-! ### Green's identities

With the divergence–Laplacian bridge in hand, Green's identities are corollaries of the divergence
theorem on any bounded `C¹` domain: for `F = u ∇v − v ∇u` the divergence is `u Δv − v Δu` (the
`∇u·∇v` cross-terms cancel), giving `∫_Ω (u Δv − v Δu) = ∫_∂Ω (u ∂ᵥv − v ∂ᵥu) dσ`. -/

/-- The real inner product on `EuclideanSpace` in coordinates. -/
lemma inner_eq_sum_coord {n : ℕ} (a b : ℝ^n) : (⟪a, b⟫ : ℝ) = ∑ i, a.ofLp i * b.ofLp i := by
  rw [PiLp.inner_apply]; exact Finset.sum_congr rfl (fun i _ => real_inner_scalars _ _)

/-- `⟪w, eᵢ⟫` reads off the `i`-th coordinate. -/
lemma inner_single_coord {n : ℕ} (w : ℝ^n) (i : Fin n) :
    (⟪w, EuclideanSpace.single i (1:ℝ)⟫ : ℝ) = w.ofLp i := by
  rw [inner_eq_sum_coord]; simp

/-- **Coordinate formula for the gradient**: `(∇f x)ᵢ = fderiv f x eᵢ`. -/
lemma gradient_ofLp {n : ℕ} {f : (ℝ^n) → ℝ} {x : ℝ^n} (hf : DifferentiableAt ℝ f x) (i : Fin n) :
    (gradient f x).ofLp i = fderiv ℝ f x (EuclideanSpace.single i 1) := by
  rw [← inner_single_coord (gradient f x) i]
  exact inner_gradient_left hf

open InnerProductSpace in
/-- **The gradient of a `C²` function is `C¹`.** -/
lemma contDiff_gradient {n : ℕ} {f : (ℝ^n) → ℝ} (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 1 (gradient f) := by
  rw [contDiff_euclidean]
  intro i
  have he : (fun x => (gradient f x).ofLp i)
      = fun x => fderiv ℝ f x (EuclideanSpace.single i 1) :=
    funext (fun x => gradient_ofLp (hf.differentiable (by norm_num) x) i)
  rw [he]
  exact (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i 1)).contDiff.comp
    (hf.fderiv_right (m := 1) (by norm_num))

/-- **Divergence is additive under subtraction.** -/
lemma divergenceE_sub {n : ℕ} (F G : (ℝ^n) → (ℝ^n)) (x : ℝ^n)
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) :
    divergenceE (fun y => F y - G y) x = divergenceE F x - divergenceE G x := by
  simp only [divergenceE]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [fderiv_fun_sub hF hG]
  simp [ContinuousLinearMap.sub_apply]

/-- **Divergence product rule** (scalar times vector field):
`div(u·G) = ⟪∇u, G⟫ + u·div G`. -/
lemma divergenceE_smul {n : ℕ} (u : (ℝ^n) → ℝ) (G : (ℝ^n) → (ℝ^n)) (x : ℝ^n)
    (hu : DifferentiableAt ℝ u x) (hG : DifferentiableAt ℝ G x) :
    divergenceE (fun y => u y • G y) x = ⟪gradient u x, G x⟫ + u x * divergenceE G x := by
  have hfd : HasFDerivAt (fun y => u y • G y)
      (u x • (fderiv ℝ G x) + (fderiv ℝ u x).smulRight (G x)) x := hu.hasFDerivAt.smul hG.hasFDerivAt
  simp only [divergenceE]
  rw [inner_eq_sum_coord, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hfd.fderiv, gradient_ofLp hu i]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, WithLp.ofLp_add, WithLp.ofLp_smul,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- **Green's second identity** on a bounded `C¹` domain: for `u, v ∈ C²`,
`∫_Ω (u Δv − v Δu) = ∫_∂Ω (u ∂ᵥv − v ∂ᵥu) dσ`. Obtained from the divergence theorem applied to
`F = u ∇v − v ∇u`, whose divergence is `u Δv − v Δu` (the `∇u·∇v` cross-terms cancel). -/
theorem green_second_identity {m : ℕ} {Ω : Set (ℝ^(m + 2))} (hΩ : IsBoundedC1Domain Ω)
    {ν : (ℝ^(m + 2)) → (ℝ^(m + 2))} (hν : IsOutwardNormal Ω ν)
    (u v : (ℝ^(m + 2)) → ℝ) (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) :
    ∫ x in Ω, (u x * Laplacian.laplacian v x - v x * Laplacian.laplacian u x)
      = ∫ x in frontier Ω, (u x * ⟪gradient v x, ν x⟫ - v x * ⟪gradient u x, ν x⟫)
          ∂(μHE[m + 1] : Measure (ℝ^(m + 2))) := by
  set F : (ℝ^(m + 2)) → (ℝ^(m + 2)) := fun y => u y • gradient v y - v y • gradient u y with hFdef
  have hgv : ContDiff ℝ 1 (gradient v) := contDiff_gradient hv
  have hgu : ContDiff ℝ 1 (gradient u) := contDiff_gradient hu
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  have hv1 : ContDiff ℝ 1 v := hv.of_le (by norm_num)
  have hFcd : ContDiff ℝ 1 F := by rw [hFdef]; exact (hu1.smul hgv).sub (hv1.smul hgu)
  have hdt := divergence_theorem hΩ hν hFcd
  have hdivF : ∀ x, divergenceE F x
      = u x * Laplacian.laplacian v x - v x * Laplacian.laplacian u x := by
    intro x
    have hud := hu1.differentiable (by norm_num) x
    have hvd := hv1.differentiable (by norm_num) x
    have hgvd := hgv.differentiable (by norm_num) x
    have hgud := hgu.differentiable (by norm_num) x
    rw [hFdef, divergenceE_sub (fun y => u y • gradient v y) (fun y => v y • gradient u y) x
        (hud.smul hgvd) (hvd.smul hgud),
      divergenceE_smul u (gradient v) x hud hgvd, divergenceE_smul v (gradient u) x hvd hgud,
      divergenceE_gradient_eq_laplacian v hv, divergenceE_gradient_eq_laplacian u hu,
      real_inner_comm (gradient v x) (gradient u x)]
    ring
  have hfluxF : ∀ x, (⟪F x, ν x⟫ : ℝ)
      = u x * ⟪gradient v x, ν x⟫ - v x * ⟪gradient u x, ν x⟫ := by
    intro x
    rw [hFdef]
    simp only [inner_sub_left, real_inner_smul_left]
  rw [setIntegral_congr_fun hΩ.measurableSet (fun x _ => hdivF x),
    setIntegral_congr_fun isClosed_frontier.measurableSet (fun x _ => hfluxF x)] at hdt
  exact hdt

/-! ### Green's identities on balls and annuli

Specializing to the ball (`isBoundedC1Domain_ball` + `isOutwardNormal_ball`, whose frontier is a
sphere and whose outward normal is `r⁻¹(y−x)`), and then to the annulus by additivity of the volume
integral (`∫_{B(x,r)\B(x,ε)} = ∫_{B(x,r)} − ∫_{B(x,ε)}`). The inner-sphere flux enters with a minus
sign because the annulus's outward normal there points into the removed ball. All surface integrals
use the Euclidean surface measure `μHE`. -/

/-- **Green's second identity on a ball.** -/
theorem green_identity_ball (x : ℝ^(m + 2)) (r : ℝ) (hr : 0 < r) (u v : (ℝ^(m + 2)) → ℝ)
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) :
    ∫ y in Metric.ball x r, (u y * Laplacian.laplacian v y - v y * Laplacian.laplacian u y)
      = ∫ y in Metric.sphere x r,
          (u y * ⟪gradient v y, r⁻¹ • (y - x)⟫ - v y * ⟪gradient u y, r⁻¹ • (y - x)⟫)
          ∂(μHE[m + 1] : Measure (ℝ^(m + 2))) := by
  have h := green_second_identity (isBoundedC1Domain_ball x r hr)
    (isOutwardNormal_ball x r hr) u v hu hv
  rwa [frontier_ball x hr.ne'] at h

/-- **Divergence theorem for the Laplacian on a ball**: `∫_B Δu = ∫_∂B ⟪∇u, ν⟫ dσ`. -/
theorem integral_laplacian_ball (x : ℝ^(m + 2)) (r : ℝ) (hr : 0 < r) (u : (ℝ^(m + 2)) → ℝ)
    (hu : ContDiff ℝ 2 u) :
    ∫ y in Metric.ball x r, Laplacian.laplacian u y
      = ∫ y in Metric.sphere x r, ⟪gradient u y, r⁻¹ • (y - x)⟫
          ∂(μHE[m + 1] : Measure (ℝ^(m + 2))) := by
  have h := divergence_theorem (isBoundedC1Domain_ball x r hr)
    (isOutwardNormal_ball x r hr) (contDiff_gradient hu)
  rw [frontier_ball x hr.ne',
    setIntegral_congr_fun (isBoundedC1Domain_ball x r hr).measurableSet
      (fun y _ => divergenceE_gradient_eq_laplacian u hu y)] at h
  exact h

/-- The Laplacian of a `C²` function is continuous. -/
lemma continuous_laplacian {f : (ℝ^(m + 2)) → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (Laplacian.laplacian f) := by
  have he : Laplacian.laplacian f = divergenceE (gradient f) :=
    funext (fun y => (divergenceE_gradient_eq_laplacian f hf y).symm)
  rw [he]; exact continuous_divergenceE (contDiff_gradient hf)

/-- **Green's second identity on an annulus** `B(x,r) \ B(x,ε)` (Euclidean surface measure). The
inner-sphere flux enters with a minus sign (its outward normal points into `B(x,ε)`). -/
theorem green_identity_annulus (x : ℝ^(m + 2)) (r ε : ℝ) (hr : 0 < r) (hε : 0 < ε) (hεr : ε < r)
    (u v : (ℝ^(m + 2)) → ℝ) (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) :
    ∫ y in Metric.ball x r \ Metric.ball x ε,
        (u y * Laplacian.laplacian v y - v y * Laplacian.laplacian u y)
      = (∫ y in Metric.sphere x r,
          (u y * ⟪gradient v y, r⁻¹ • (y - x)⟫ - v y * ⟪gradient u y, r⁻¹ • (y - x)⟫)
          ∂(μHE[m + 1] : Measure (ℝ^(m + 2))))
      - (∫ y in Metric.sphere x ε,
          (u y * ⟪gradient v y, ε⁻¹ • (y - x)⟫ - v y * ⟪gradient u y, ε⁻¹ • (y - x)⟫)
          ∂(μHE[m + 1] : Measure (ℝ^(m + 2)))) := by
  have hcont : Continuous (fun y => u y * Laplacian.laplacian v y - v y * Laplacian.laplacian u y) :=
    (hu.continuous.mul (continuous_laplacian hv)).sub (hv.continuous.mul (continuous_laplacian hu))
  have hint : IntegrableOn (fun y => u y * Laplacian.laplacian v y - v y * Laplacian.laplacian u y)
      (Metric.ball x r) :=
    (hcont.locallyIntegrable.integrableOn_isCompact (isCompact_closedBall x r)).mono_set
      Metric.ball_subset_closedBall
  rw [setIntegral_diff measurableSet_ball hint (Metric.ball_subset_ball hεr.le),
    green_identity_ball x r hr u v hu hv, green_identity_ball x ε hε u v hu hv]

/-- **Green's first identity** on a bounded `C¹` domain: for `u, v ∈ C²`,
`∫_Ω (u Δv + ⟪∇u,∇v⟫) = ∫_∂Ω u ⟪∇v,ν⟫ dσ`. Obtained from the divergence theorem applied to
`F = u ∇v`, whose divergence is `⟪∇u,∇v⟫ + u Δv`. -/
theorem green_first_identity {Ω : Set (ℝ^(m + 2))} (hΩ : IsBoundedC1Domain Ω)
    {ν : (ℝ^(m + 2)) → (ℝ^(m + 2))} (hν : IsOutwardNormal Ω ν)
    (u v : (ℝ^(m + 2)) → ℝ) (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) :
    ∫ x in Ω, (u x * Laplacian.laplacian v x + ⟪gradient u x, gradient v x⟫)
      = ∫ x in frontier Ω, u x * ⟪gradient v x, ν x⟫
          ∂(μHE[m + 1] : Measure (ℝ^(m + 2))) := by
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  have hgv : ContDiff ℝ 1 (gradient v) := contDiff_gradient hv
  have hdt := divergence_theorem hΩ hν (F := fun y => u y • gradient v y) (hu1.smul hgv)
  have hdiv : ∀ x, divergenceE (fun y => u y • gradient v y) x
      = u x * Laplacian.laplacian v x + ⟪gradient u x, gradient v x⟫ := by
    intro x
    rw [divergenceE_smul u (gradient v) x (hu1.differentiable (by norm_num) x)
        (hgv.differentiable (by norm_num) x), divergenceE_gradient_eq_laplacian v hv]
    ring
  have hflux : ∀ x, (⟪(fun y => u y • gradient v y) x, ν x⟫ : ℝ) = u x * ⟪gradient v x, ν x⟫ :=
    fun x => real_inner_smul_left _ _ _
  rw [setIntegral_congr_fun hΩ.measurableSet (fun x _ => hdiv x),
    setIntegral_congr_fun isClosed_frontier.measurableSet (fun x _ => hflux x)] at hdt
  exact hdt

/-- **Green's first identity on a ball.** -/
theorem green_first_identity_ball (x : ℝ^(m + 2)) (r : ℝ) (hr : 0 < r) (u v : (ℝ^(m + 2)) → ℝ)
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) :
    ∫ y in Metric.ball x r, (u y * Laplacian.laplacian v y + ⟪gradient u y, gradient v y⟫)
      = ∫ y in Metric.sphere x r, u y * ⟪gradient v y, r⁻¹ • (y - x)⟫
          ∂(μHE[m + 1] : Measure (ℝ^(m + 2))) := by
  have h := green_first_identity (isBoundedC1Domain_ball x r hr)
    (isOutwardNormal_ball x r hr) u v hu hv
  rwa [frontier_ball x hr.ne'] at h

/-! ### Rescaling surface integrals to the unit sphere

The dilation `ω ↦ x + r•ω` maps `∂B(0,1)` onto `∂B(x,r)` and scales the `(m+1)`-dimensional surface
measure by `r^(m+1)`. This reduces any surface integral over `∂B(x,r)` to the fixed unit sphere — the
change of variables underlying differentiation of spherical means. -/

/-- `μHE[d]` scales by `‖c‖^d` under dilation (from the raw Hausdorff scaling). -/
lemma μHE_smul_set {d : ℕ} {c : ℝ} (hc : c ≠ 0) (s : Set (ℝ^(m + 2))) :
    (μHE[d] : Measure (ℝ^(m + 2))) (c • s) = (‖c‖₊ : ℝ≥0∞) ^ d * μHE[d] s := by
  rw [euclideanHausdorffMeasure_def, Measure.smul_apply, Measure.smul_apply,
    hausdorffMeasure_smul₀ (by positivity) hc, NNReal.rpow_natCast]
  simp only [ENNReal.smul_def, ENNReal.coe_pow, smul_eq_mul]
  ring

/-- `μHE[d]` is translation-invariant. -/
lemma μHE_vadd_set {d : ℕ} (x : ℝ^(m + 2)) (s : Set (ℝ^(m + 2))) :
    (μHE[d] : Measure (ℝ^(m + 2))) ((fun y => x + y) '' s) = μHE[d] s :=
  (isometry_add_left x).euclideanHausdorffMeasure_image s

/-- Pushforward of `μHE` under a dilation `r • ·`. -/
lemma map_smul_μHE {d : ℕ} {r : ℝ} (hr : r ≠ 0) :
    Measure.map (fun ω : ℝ^(m + 2) => r • ω) (μHE[d] : Measure (ℝ^(m + 2)))
      = ((‖(r⁻¹ : ℝ)‖₊ : ℝ≥0∞) ^ d) • μHE[d] := by
  ext s hs
  rw [Measure.map_apply (measurable_const_smul r) hs, Measure.smul_apply, smul_eq_mul,
    Set.preimage_smul₀ hr, μHE_smul_set (inv_ne_zero hr)]

/-- Pushforward of `μHE` under a translation (invariant). -/
lemma map_add_μHE {d : ℕ} (x : ℝ^(m + 2)) :
    Measure.map (fun z : ℝ^(m + 2) => x + z) (μHE[d] : Measure (ℝ^(m + 2))) = μHE[d] := by
  ext s hs
  rw [Measure.map_apply (measurable_const_add x) hs]
  have hpre : (fun z : ℝ^(m + 2) => x + z) ⁻¹' s = (fun y => -x + y) '' s := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · intro h; exact ⟨x + ω, h, by abel⟩
    · rintro ⟨w, hw, rfl⟩; rwa [← add_assoc, add_neg_cancel, zero_add]
  rw [hpre, μHE_vadd_set]

set_option maxHeartbeats 1000000 in
-- The `EuclideanSpace`/measure manipulation repeatedly forces slow normalization, exceeding the
-- default heartbeat budget.
/-- **Surface-integral rescaling.** For `r > 0`, integrating over `∂B(x,r)` reduces to the unit
sphere by the dilation `ω ↦ x + r•ω`, with the Jacobian factor `r^(m+1)`. -/
theorem setIntegral_sphere_rescale (x : ℝ^(m + 2)) {r : ℝ} (hr : 0 < r) (f : (ℝ^(m + 2)) → ℝ) :
    ∫ y in Metric.sphere x r, f y ∂(μHE[m + 1] : Measure (ℝ^(m + 2)))
      = r ^ (m + 1) • ∫ ω in Metric.sphere (0 : ℝ^(m + 2)) 1, f (x + r • ω)
          ∂(μHE[m + 1] : Measure (ℝ^(m + 2))) := by
  set g : (ℝ^(m + 2)) → (ℝ^(m + 2)) := fun ω => x + r • ω with hgdef
  have hgemb : MeasurableEmbedding g :=
    ((Homeomorph.smulOfNeZero r hr.ne').trans (Homeomorph.addLeft x)).measurableEmbedding
  have hmap : Measure.map g (μHE[m + 1] : Measure (ℝ^(m + 2)))
      = ((‖(r⁻¹ : ℝ)‖₊ : ℝ≥0∞) ^ (m + 1)) • μHE[m + 1] := by
    have hcomp : g = (fun z => x + z) ∘ (fun ω => r • ω) := rfl
    rw [hcomp, ← Measure.map_map (measurable_const_add x) (measurable_const_smul r),
      map_smul_μHE hr.ne', Measure.map_smul, map_add_μHE]
  have hpreimage : g ⁻¹' (Metric.sphere x r) = Metric.sphere (0 : ℝ^(m + 2)) 1 := by
    ext ω
    simp only [hgdef, Set.mem_preimage, Metric.mem_sphere, dist_eq_norm, add_sub_cancel_left,
      norm_smul, Real.norm_eq_abs, abs_of_pos hr, sub_zero]
    constructor
    · intro h; exact mul_left_cancel₀ hr.ne' (by rw [h, mul_one])
    · intro h; rw [h, mul_one]
  have h1 := hgemb.setIntegral_map (μ := (μHE[m + 1] : Measure (ℝ^(m + 2)))) f (Metric.sphere x r)
  rw [hmap, hpreimage] at h1
  simp only [Measure.restrict_smul, integral_smul_measure] at h1
  have hc : ((‖(r⁻¹ : ℝ)‖₊ : ℝ≥0∞) ^ (m + 1)).toReal = (r ^ (m + 1))⁻¹ := by
    rw [ENNReal.toReal_pow, ENNReal.coe_toReal, coe_nnnorm, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr), ← inv_pow]
  rw [hc] at h1
  simp only [hgdef] at h1
  rw [← h1, smul_smul, mul_inv_cancel₀ (by positivity : (r : ℝ) ^ (m + 1) ≠ 0), one_smul]

/-- **Average rescaling.** The spherical average over `∂B(x,r)` equals the average over the unit
sphere of `ω ↦ f(x + r•ω)` (the `r^(m+1)` Jacobian cancels in the average). -/
theorem setAverage_sphere_rescale (x : ℝ^(m + 2)) {r : ℝ} (hr : 0 < r) (f : (ℝ^(m + 2)) → ℝ) :
    ⨍ y in Metric.sphere x r, f y ∂(μHE[m + 1] : Measure (ℝ^(m + 2)))
      = ⨍ ω in Metric.sphere (0 : ℝ^(m + 2)) 1, f (x + r • ω)
          ∂(μHE[m + 1] : Measure (ℝ^(m + 2))) := by
  have hmeas : (μHE[m + 1] (Metric.sphere x r)).toReal
      = r ^ (m + 1) * (μHE[m + 1] (Metric.sphere (0 : ℝ^(m + 2)) 1)).toReal := by
    have h := setIntegral_sphere_rescale x hr (fun _ : ℝ^(m + 2) => (1:ℝ))
    simpa [setIntegral_const, smul_eq_mul] using h
  have hcancel : (r ^ (m + 1) * (μHE[m + 1] (Metric.sphere (0 : ℝ^(m + 2)) 1)).toReal)⁻¹ * r ^ (m + 1)
      = (μHE[m + 1] (Metric.sphere (0 : ℝ^(m + 2)) 1)).toReal⁻¹ := by
    rw [_root_.mul_inv_rev, mul_assoc, inv_mul_cancel₀ (by positivity : (r : ℝ) ^ (m + 1) ≠ 0),
      mul_one]
  rw [setAverage_eq, setAverage_eq, setIntegral_sphere_rescale x hr f]
  simp only [measureReal_def]
  rw [hmeas, smul_smul, hcancel]

set_option maxHeartbeats 1000000 in
-- Differentiation under the integral over the unit sphere repeatedly normalizes `EuclideanSpace`
-- projections and measure terms, exceeding the default heartbeat budget.
/-- **Derivative of the (unnormalized) spherical mean.** Differentiating under the integral over the
fixed unit sphere: `d/ds ∫_{∂B(0,1)} u(x+sω) dσ = ∫_{∂B(0,1)} ⟪∇u(x+sω), ω⟫ dσ`. -/
theorem hasDerivAt_sphere_integral (x : ℝ^(m + 2)) (u : (ℝ^(m + 2)) → ℝ) (hu : ContDiff ℝ 2 u)
    (s₀ : ℝ) :
    HasDerivAt (fun s => ∫ ω in Metric.sphere (0 : ℝ^(m + 2)) 1, u (x + s • ω)
        ∂(μHE[m + 1] : Measure (ℝ^(m + 2))))
      (∫ ω in Metric.sphere (0 : ℝ^(m + 2)) 1, ⟪gradient u (x + s₀ • ω), ω⟫
        ∂(μHE[m + 1] : Measure (ℝ^(m + 2)))) s₀ := by
  set μ := (μHE[m + 1] : Measure (ℝ^(m + 2))).restrict (Metric.sphere (0 : ℝ^(m + 2)) 1) with hμ
  have hfin : (μHE[m + 1] : Measure (ℝ^(m + 2))) (Metric.sphere (0 : ℝ^(m + 2)) 1) < ⊤ := by
    have h := surfaceMeasure_frontier_lt_top (isBoundedC1Domain_ball (0 : ℝ^(m + 2)) 1 one_pos)
    rwa [frontier_ball (0 : ℝ^(m + 2)) one_ne_zero] at h
  haveI : IsFiniteMeasure μ := ⟨by rw [hμ, Measure.restrict_apply_univ]; exact hfin⟩
  set K : Set (ℝ^(m + 2)) := (fun p : ℝ × (ℝ^(m + 2)) => x + p.1 • p.2)
    '' (Set.Icc (s₀ - 1) (s₀ + 1) ×ˢ Metric.sphere (0 : ℝ^(m + 2)) 1) with hK
  have hKc : IsCompact K :=
    (isCompact_Icc.prod (isCompact_sphere (0 : ℝ^(m + 2)) 1)).image
      (continuous_const.add (continuous_fst.smul continuous_snd))
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn (contDiff_gradient hu).continuous.continuousOn
  have hmemK : ∀ s ∈ Metric.ball s₀ 1, ∀ ω ∈ Metric.sphere (0 : ℝ^(m + 2)) 1, x + s • ω ∈ K := by
    intro s hs ω hω
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hs
    exact ⟨(s, ω), ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩, hω⟩, rfl⟩
  have hcont₀ : Continuous (fun ω : ℝ^(m + 2) => u (x + s₀ • ω)) :=
    hu.continuous.comp (continuous_const.add (continuous_const.smul continuous_id))
  have hdiff : ∀ ω : ℝ^(m + 2), ∀ s : ℝ,
      HasDerivAt (fun s => u (x + s • ω)) (⟪gradient u (x + s • ω), ω⟫) s := by
    intro ω s
    have hline : HasDerivAt (fun t : ℝ => x + t • ω) ω s := by
      simpa using ((hasDerivAt_id (x := s)).smul_const ω).const_add x
    have hcomp := (hu.differentiable (by norm_num) (x + s • ω)).hasFDerivAt.comp_hasDerivAt s hline
    rwa [inner_gradient_left (hu.differentiable (by norm_num) _)]
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun _ => C)
    (F := fun s ω => u (x + s • ω)) (F' := fun s ω => ⟪gradient u (x + s • ω), ω⟫)
    (ball_mem_nhds s₀ one_pos) ?_ ?_ ?_ ?_ (integrable_const C) ?_).2
  · refine Filter.Eventually.of_forall (fun s => ?_)
    exact (hu.continuous.comp
      (continuous_const.add (continuous_const.smul continuous_id))).aestronglyMeasurable
  · obtain ⟨M, hM⟩ := (isCompact_sphere (0 : ℝ^(m + 2)) 1).exists_bound_of_continuousOn
      hcont₀.continuousOn
    refine (integrable_const M).mono' hcont₀.aestronglyMeasurable
      (ae_restrict_of_forall_mem isClosed_sphere.measurableSet (fun ω hω => ?_))
    exact hM ω hω
  · have hcont : Continuous (fun ω : ℝ^(m + 2) => ⟪gradient u (x + s₀ • ω), ω⟫) :=
      ((contDiff_gradient hu).continuous.comp
        (continuous_const.add (continuous_const.smul continuous_id))).inner continuous_id
    exact hcont.aestronglyMeasurable
  · refine (ae_restrict_of_forall_mem isClosed_sphere.measurableSet (fun ω hω => ?_))
    intro s hs
    calc ‖(⟪gradient u (x + s • ω), ω⟫ : ℝ)‖ ≤ ‖gradient u (x + s • ω)‖ * ‖ω‖ :=
          norm_inner_le_norm _ _
      _ = ‖gradient u (x + s • ω)‖ := by
          rw [Metric.mem_sphere, dist_zero_right] at hω; rw [hω, mul_one]
      _ ≤ C := hC _ (hmemK s hs ω hω)
  · exact Filter.Eventually.of_forall (fun ω s _ => hdiff ω s)

/-! ### The mean-value property for harmonic functions

Assembling the pieces: the spherical mean `⨍_{∂B(x,s)} u` equals `⨍_{∂B(0,1)} u(x+sω)`, whose
`s`-derivative is `(1/σ)∫_{∂B(0,1)} ⟪∇u(x+sω),ω⟫`; that flux integral equals `s^{-(m+1)}∫_B Δu` (via
`integral_laplacian_ball`), which vanishes for harmonic `u`. Hence the mean is constant in `s`, and
its value at `s→0` is `u(x)`. -/

/-- For a function harmonic on `closedBall x s`, the derivative of the spherical mean vanishes:
`∫_{∂B(0,1)} ⟪∇u(x+sω), ω⟫ dσ = 0`. -/
theorem sphere_integral_grad_eq_zero (x : ℝ^(m + 2)) {s : ℝ} (hs : 0 < s) (u : (ℝ^(m + 2)) → ℝ)
    (hu : ContDiff ℝ 2 u) (hΔ : ∀ y ∈ Metric.closedBall x s, Laplacian.laplacian u y = 0) :
    ∫ ω in Metric.sphere (0 : ℝ^(m + 2)) 1, ⟪gradient u (x + s • ω), ω⟫
      ∂(μHE[m + 1] : Measure (ℝ^(m + 2))) = 0 := by
  have hΔ0 : ∫ y in Metric.ball x s, Laplacian.laplacian u y
      ∂(volume : Measure (ℝ^(m + 2))) = 0 := by
    rw [setIntegral_congr_fun measurableSet_ball
      (fun y hy => hΔ y (Metric.ball_subset_closedBall hy))]
    simp
  have hlap := integral_laplacian_ball x s hs u hu
  rw [hΔ0] at hlap
  have hrescale := setIntegral_sphere_rescale x hs
    (fun y => (⟪gradient u y, s⁻¹ • (y - x)⟫ : ℝ))
  rw [← hlap] at hrescale
  have hsimp : ∀ ω : ℝ^(m + 2),
      (⟪gradient u (x + s • ω), s⁻¹ • ((x + s • ω) - x)⟫ : ℝ)
        = ⟪gradient u (x + s • ω), ω⟫ := by
    intro ω
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hs.ne', one_smul]
  simp only [hsimp] at hrescale
  exact (smul_eq_zero.mp hrescale.symm).resolve_left (pow_pos hs (m + 1)).ne'

/-- The unit sphere has positive (finite) surface measure. -/
lemma sphere_surfaceMeasure_pos : 0 < ((μHE[m + 1] : Measure (ℝ^(m + 2)))
    (Metric.sphere (0 : ℝ^(m + 2)) 1)).toReal := by
  rw [sphere_surfaceMeasure (0 : ℝ^(m + 2)) 1 one_pos]
  have hvol : 0 < (volume (Metric.ball (0 : ℝ^(m + 2)) 1)).toReal := by
    rw [ENNReal.toReal_pos_iff]
    exact ⟨measure_ball_pos volume 0 one_pos, measure_ball_lt_top⟩
  positivity

/-- **Mean-value property (μHE surface measure).** A function harmonic on `closedBall x r` equals
its spherical average over `∂B(x,r)`. -/
theorem harmonic_sphereMean_μHE (x : ℝ^(m + 2)) (r : ℝ) (hr : 0 < r) (u : (ℝ^(m + 2)) → ℝ)
    (hu : ContDiff ℝ 2 u) (hΔ : ∀ y ∈ Metric.closedBall x r, Laplacian.laplacian u y = 0) :
    u x = ⨍ y in Metric.sphere x r, u y ∂(μHE[m + 1] : Measure (ℝ^(m + 2))) := by
  set Φ : ℝ → ℝ := fun s => ∫ ω in Metric.sphere (0 : ℝ^(m + 2)) 1, u (x + s • ω) ∂μHE[m + 1]
    with hΦ
  set d : ℝ → ℝ := fun s => ∫ ω in Metric.sphere (0 : ℝ^(m + 2)) 1,
    ⟪gradient u (x + s • ω), ω⟫ ∂μHE[m + 1] with hd
  have hΦderiv : ∀ s, HasDerivAt Φ (d s) s := fun s => hasDerivAt_sphere_integral x u hu s
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope Φ d hr
    (fun s _ => (hΦderiv s).continuousAt.continuousWithinAt) (fun s _ => hΦderiv s)
  have hdc : d c = 0 := sphere_integral_grad_eq_zero x hc.1 u hu
    (fun y hy => hΔ y (Metric.closedBall_subset_closedBall hc.2.le hy))
  have hΦeq : Φ r = Φ 0 := by
    have h0 : (Φ r - Φ 0) / (r - 0) = 0 := by rw [← hslope, hdc]
    rw [div_eq_zero_iff] at h0
    rcases h0 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd (by linarith : r = 0) hr.ne'
  rw [setAverage_sphere_rescale x hr u, setAverage_eq]
  have hΦ0 : (∫ ω in Metric.sphere (0 : ℝ^(m + 2)) 1, u (x + r • ω) ∂μHE[m + 1])
      = (μHE[m + 1] (Metric.sphere (0 : ℝ^(m + 2)) 1)).toReal • u x := by
    calc (∫ ω in Metric.sphere (0 : ℝ^(m + 2)) 1, u (x + r • ω) ∂μHE[m + 1])
        = ∫ ω in Metric.sphere (0 : ℝ^(m + 2)) 1, u (x + (0:ℝ) • ω) ∂μHE[m + 1] := hΦeq
      _ = ∫ ω in Metric.sphere (0 : ℝ^(m + 2)) 1, u x ∂μHE[m + 1] := by
          simp only [zero_smul, add_zero]
      _ = (μHE[m + 1] (Metric.sphere (0 : ℝ^(m + 2)) 1)).toReal • u x := setIntegral_const (u x)
  rw [hΦ0]
  simp only [measureReal_def]
  rw [smul_smul, inv_mul_cancel₀ sphere_surfaceMeasure_pos.ne', one_smul]

end

end AreaFormula


open MeasureTheory InnerProductSpace Set Laplacian Topology
open scoped ENNReal NNReal

/-! ### Scaling invariance of averages

The average `⨍` is unchanged when the underlying measure is scaled by a nonzero finite constant.
This is the bridge between the Riemannian surface measure `μHE[d]` (`= c₀ • μH[d]`, `c₀ ≠ 0, ∞`)
used by the divergence theorem and the raw Hausdorff measure `μH[d]` used to define `sphereMean`. -/

/-- The average is invariant under scaling the measure by a nonzero finite constant. -/
lemma average_smul_measure' {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [NormedSpace ℝ E] {c : ℝ≥0∞} (hc : c ≠ 0) (hc' : c ≠ ∞) (μ : Measure α) (f : α → E) :
    average (c • μ) f = average μ f := by
  have hct : c.toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hc, hc'⟩
  rw [average_eq, average_eq, integral_smul_measure]
  simp only [measureReal_def, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul]
  rw [smul_smul]
  congr 1
  rw [mul_inv_rev, mul_assoc, inv_mul_cancel₀ hct, mul_one]

/-- Set-average is invariant under scaling the measure by a nonzero finite constant. -/
lemma setAverage_smul_measure' {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [NormedSpace ℝ E] {c : ℝ≥0∞} (hc : c ≠ 0) (hc' : c ≠ ∞) (μ : Measure α) (s : Set α)
    (f : α → E) :
    (⨍ y in s, f y ∂(c • μ)) = ⨍ y in s, f y ∂μ := by
  rw [Measure.restrict_smul, average_smul_measure' hc hc']

/-- Scaling a measure by an `ℝ≥0` constant equals scaling by its `ℝ≥0∞` coercion. -/
lemma nnreal_smul_measure_eq {α : Type*} [MeasurableSpace α] (c : ℝ≥0) (μ : Measure α) :
    (c • μ) = (↑c : ℝ≥0∞) • μ := by
  ext s hs
  rw [Measure.smul_apply, Measure.smul_apply, ENNReal.smul_def]

/-- Set-average is invariant under scaling the measure by a nonzero `ℝ≥0` constant. -/
lemma setAverage_nnreal_smul {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [NormedSpace ℝ E] {c : ℝ≥0} (hc : c ≠ 0) (μ : Measure α) (s : Set α) (f : α → E) :
    (⨍ y in s, f y ∂((c : ℝ≥0) • μ)) = ⨍ y in s, f y ∂μ := by
  rw [nnreal_smul_measure_eq, setAverage_smul_measure' (ENNReal.coe_ne_zero.mpr hc)
    ENNReal.coe_ne_top]

/-- The Riemannian surface measure `μHE[d]` and the raw Hausdorff measure `μH[d]` give the same
    set-average: they differ only by the nonzero finite scalar `c₀ = addHaarScalarFactor …`. -/
lemma setAverage_μHE_eq_μH {X : Type*} [MeasurableSpace X] [EMetricSpace X] [BorelSpace X]
    (d : ℕ) (s : Set X) (f : X → ℝ) :
    (⨍ y in s, f y ∂(μHE[d] : Measure X)) = ⨍ y in s, f y ∂(μH[(d : ℝ)] : Measure X) := by
  rw [Measure.euclideanHausdorffMeasure_def]
  exact setAverage_nnreal_smul
    (Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero d) _ _ _

/-!
# Laplace and Poisson Equations (Evans PDE, §2.2)

Formalizing classical solutions to:

  (Laplace)  −Δu = 0   in U ⊆ ℝⁿ
  (Poisson)  −Δu = f   in U ⊆ ℝⁿ

Key results:
* Fundamental solution `Φ(x)` — the "building block" for solving Poisson's equation
* Representation formula: `u(x) = ∫ Φ(x−y) f(y) dy` (Newtonian potential)
* Mean value property: harmonic ↔ `u(x) = avgᵣ u` on spheres/balls
* Maximum principle: harmonic functions attain max/min on the boundary

## References
* Evans, Lawrence C. *Partial Differential Equations*, 2nd ed., §2.2.
-/

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-! ### The PDEs -/

/-- `u` is harmonic on the open set `U`: `Δu = 0` in `U` pointwise. -/
def IsHarmonic (U : Set ℝⁿ) (u : ℝⁿ → ℝ) : Prop :=
  ∀ x ∈ U, Δ u x = 0

/-- `u` solves Poisson's equation `−Δu = f` on `U`. -/
def IsPoissonSolution (U : Set ℝⁿ) (f : ℝⁿ → ℝ) (u : ℝⁿ → ℝ) : Prop :=
  ∀ x ∈ U, -Δ u x = f x

/-- Laplace's equation is Poisson's equation with `f = 0`. -/
lemma isHarmonic_iff_isPoissonSolution_zero (U : Set ℝⁿ) (u : ℝⁿ → ℝ) :
    IsHarmonic U u ↔ IsPoissonSolution U 0 u := by
  simp [IsHarmonic, IsPoissonSolution, neg_eq_zero]

/-! ### Fundamental Solution -/

/-- The fundamental solution of the Laplacian (Evans §2.2.1).

    For `n ≥ 3`: `Φ(x) = 1 / (n(n−2)ωₙ) · |x|^(2−n)`
    For `n = 2`: `Φ(x) = −1/(2π) · log |x|`
    where `ωₙ` is the volume of the unit ball in `ℝⁿ`.

    `Φ` is defined for `x ≠ 0` and satisfies `−ΔΦ = δ₀` in the distributional sense. -/
noncomputable def fundamentalSolution : ℝⁿ → ℝ :=
  fun x =>
    if n = 0 then 0
    else if n = 1 then (1 / 2 : ℝ) * ‖x‖
    else if n = 2 then -(1 / (2 * Real.pi)) * Real.log ‖x‖
    else
      let d : ℝ := (n : ℝ)
      let ω : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal
      (1 / (d * (d - 2) * ω)) * ‖x‖ ^ (2 - d)

/-! ### Newtonian Potential -/

/-- The Newtonian potential: `u(x) = ∫ Φ(x − y) f(y) dy`.
    This is the convolution of the fundamental solution with the source `f`. -/
noncomputable def newtonianPotential (f : ℝⁿ → ℝ) : ℝⁿ → ℝ :=
  fun x => ∫ y, fundamentalSolution (x - y) * f y

/-! ### Mean Value Property -/

/-- The mean value on the sphere `∂B(x, r)` using the `(n−1)`-dimensional Hausdorff measure,
    i.e., the surface area measure on `∂B(x, r)`. -/
noncomputable def sphereMean (u : ℝⁿ → ℝ) (x : ℝⁿ) (r : ℝ) : ℝ :=
  ⨍ y in Metric.sphere x r, u y ∂(Measure.hausdorffMeasure ((n : ℝ) - 1))

/-- The mean value on the ball `B(x, r)` using the Lebesgue measure. -/
noncomputable def ballMean (u : ℝⁿ → ℝ) (x : ℝⁿ) (r : ℝ) : ℝ :=
  ⨍ y in Metric.ball x r, u y

/-- **Mean Value Property (sphere version)** (Evans §2.2.2, Theorem 2).

    Stated for `n ≥ 2`, the substantive setting of Evans §2.2 (the fundamental solution is defined
    for `n ≥ 2`); `n = 1` is a degenerate affine case and `n = 0` is false (the sphere is empty). -/
theorem harmonic_sphereMeanValue (hn : 2 ≤ n) (U : Set ℝⁿ) (u : ℝⁿ → ℝ)
    (hU : IsOpen U) (hu : IsHarmonic U u) (hu_c2 : ContDiff ℝ 2 u)
    (x : ℝⁿ) (r : ℝ) (hr : 0 < r)
    (hball : Metric.closedBall x r ⊆ U) :
    u x = sphereMean u x r := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hΔ : ∀ y ∈ Metric.closedBall x r, Laplacian.laplacian u y = 0 :=
    fun y hy => hu y (hball hy)
  rw [AreaFormula.harmonic_sphereMean_μHE x r hr u hu_c2 hΔ, sphereMean,
    show ((m + 2 : ℕ) : ℝ) - 1 = ((m + 1 : ℕ) : ℝ) by push_cast; ring,
    setAverage_μHE_eq_μH]

/-- **Mean Value Property (ball version)** (Evans §2.2.2, Theorem 2). -/
theorem harmonic_ballMeanValue (U : Set ℝⁿ) (u : ℝⁿ → ℝ)
    (hU : IsOpen U) (hu : IsHarmonic U u) (hu_c2 : ContDiff ℝ 2 u)
    (x : ℝⁿ) (r : ℝ) (hr : 0 < r)
    (hball : Metric.closedBall x r ⊆ U) :
    u x = ballMean u x r := by
  sorry

/-- **Converse**: mean value property implies harmonic. -/
theorem meanValue_implies_harmonic (U : Set ℝⁿ) (u : ℝⁿ → ℝ)
    (hU : IsOpen U) (hu_c2 : ContDiff ℝ 2 u)
    (hmv : ∀ x ∈ U, ∀ r > 0, Metric.closedBall x r ⊆ U → u x = ballMean u x r) :
    IsHarmonic U u := by
  sorry

/-! ### Maximum Principle -/

/-- **Strong Maximum Principle** (Evans §2.2.3, Theorem 4). -/
theorem harmonic_strongMax (U : Set ℝⁿ) (u : ℝⁿ → ℝ)
    (hU : IsOpen U) (hconn : IsConnected U)
    (hu : IsHarmonic U u) (hu_c : Continuous u)
    (x₀ : ℝⁿ) (hx₀ : x₀ ∈ U)
    (hmax : ∀ x ∈ U, u x ≤ u x₀) :
    ∀ x ∈ U, u x = u x₀ := by
  sorry

/-- **Weak Maximum Principle** (Evans §2.2.3, Theorem 3). A `C²` harmonic function on a
    bounded open set attains its supremum on the boundary. Proved by the standard subharmonic
    perturbation `v_ε = u + ε‖·‖²` (`Δv_ε = 2nε > 0`, so by `laplacian_nonpos_of_isLocalMax` it
    has no interior maximum), then letting `ε → 0`. -/
theorem harmonic_weakMax (U : Set ℝⁿ) (u : ℝⁿ → ℝ)
    (hn : 1 ≤ n) (hU : IsOpen U) (hbdd : Bornology.IsBounded U)
    (hu : IsHarmonic U u) (hu_c2 : ContDiff ℝ 2 u) :
    ∀ x ∈ U, u x ≤ sSup (u '' frontier U) := by
  have hK : IsCompact (closure U) := hbdd.isCompact_closure
  have hcont : Continuous u := hu_c2.continuous
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨R, hR⟩ := (hbdd.closure).subset_closedBall (0 : ℝⁿ)
  have hRnorm : ∀ y ∈ closure U, ‖y‖ ≤ R := fun y hy => by
    simpa [Metric.mem_closedBall, dist_zero_right] using hR hy
  have hfrontK : IsCompact (frontier U) :=
    hK.of_isClosed_subset isClosed_frontier frontier_subset_closure
  have hBdd : BddAbove (u '' frontier U) := (hfrontK.image hcont).bddAbove
  set M := sSup (u '' frontier U) with hM
  intro x hx
  have key : ∀ ε : ℝ, 0 < ε → u x ≤ M + ε * R ^ 2 := by
    intro ε hε
    set v : ℝⁿ → ℝ := fun y => u y + ε * ‖y‖ ^ 2 with hv
    have hvcont : Continuous v := by fun_prop
    obtain ⟨xs, hxs_mem, hxs_max⟩ :=
      hK.exists_isMaxOn ⟨x, subset_closure hx⟩ hvcont.continuousOn
    have hxs_notU : xs ∉ U := by
      intro hxsU
      have hlm : IsLocalMax v xs :=
        hxs_max.isLocalMax (Filter.mem_of_superset (hU.mem_nhds hxsU) subset_closure)
      have hvadd : v = u + fun y : ℝⁿ => ε * ‖y‖ ^ 2 := by
        funext y; simp only [hv, Pi.add_apply]
      have hsq2 : ContDiffAt ℝ 2 (fun y : ℝⁿ => ‖y‖ ^ 2) xs :=
        (contDiff_norm_sq ℝ : ContDiff ℝ 2 fun y : ℝⁿ => ‖y‖ ^ 2).contDiffAt
      have h2 : ContDiffAt ℝ 2 (fun y : ℝⁿ => ε * ‖y‖ ^ 2) xs := hsq2.const_smul ε
      have hvc2 : ContDiffAt ℝ 2 v xs := by rw [hvadd]; exact hu_c2.contDiffAt.add h2
      have hle : Laplacian.laplacian v xs ≤ 0 := laplacian_nonpos_of_isLocalMax hvc2 hlm
      have hΔ : Laplacian.laplacian v xs = Laplacian.laplacian u xs + ε * (2 * (n : ℝ)) := by
        rw [hvadd, ContDiffAt.laplacian_add hu_c2.contDiffAt h2]
        congr 1
        have hsmul : (fun y : ℝⁿ => ε * ‖y‖ ^ 2) = ε • fun y : ℝⁿ => ‖y‖ ^ 2 := by
          funext y; simp [Pi.smul_apply, smul_eq_mul]
        rw [hsmul, laplacian_smul ε hsq2, laplacian_norm_sq, smul_eq_mul]
      rw [hΔ, hu xs hxsU, zero_add] at hle
      exact absurd hle (not_le.mpr (mul_pos hε (mul_pos two_pos hnpos)))
    have hxs_front : xs ∈ frontier U :=
      ⟨hxs_mem, by rw [hU.interior_eq]; exact hxs_notU⟩
    have h1 : u x ≤ v x := by rw [hv]; nlinarith [sq_nonneg ‖x‖, hε]
    have h2 : v x ≤ v xs := hxs_max (subset_closure hx)
    have h4 : u xs ≤ M := le_csSup hBdd ⟨xs, hxs_front, rfl⟩
    have h5 : ‖xs‖ ^ 2 ≤ R ^ 2 := by nlinarith [hRnorm xs hxs_mem, norm_nonneg xs]
    calc u x ≤ v x := h1
      _ ≤ v xs := h2
      _ = u xs + ε * ‖xs‖ ^ 2 := rfl
      _ ≤ M + ε * R ^ 2 := by nlinarith [h4, h5, hε.le]
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have hR1 : (0 : ℝ) < R ^ 2 + 1 := by positivity
  have hk := key (δ / (R ^ 2 + 1)) (by positivity)
  have hbound : δ / (R ^ 2 + 1) * R ^ 2 ≤ δ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hR1]; nlinarith [hδ.le]
  linarith [hk, hbound]

/-! ### Smoothness of Harmonic Functions -/

/-- **Regularity** (Evans §2.2.3, Theorem 6). -/
theorem harmonic_smooth (U : Set ℝⁿ) (u : ℝⁿ → ℝ)
    (hU : IsOpen U) (hu : IsHarmonic U u) (hu_c2 : ContDiffOn ℝ 2 u U) :
    ContDiffOn ℝ ⊤ u U := by
  sorry

/-! ### Representation Formula for Poisson's Equation -/

/-! #### Intermediate Lemmas (Evans §2.2.4 proof steps) -/

/-- `fundamentalSolution` is smooth on `ℝⁿ \ {0}`. -/
lemma fundamentalSolution_contDiff_off_zero :
    ContDiffOn ℝ ⊤ (fundamentalSolution (n := n)) ({0} : Set ℝⁿ)ᶜ := by
  have hn_smooth : ContDiffOn ℝ ⊤ (fun x : ℝⁿ => ‖x‖) ({0} : Set ℝⁿ)ᶜ :=
    fun x hx => (contDiffAt_norm ℝ (Set.mem_compl_singleton_iff.mp hx)).contDiffWithinAt
  have hn_ne : ∀ x ∈ ({0} : Set ℝⁿ)ᶜ, ‖x‖ ≠ 0 :=
    fun x hx => (norm_pos_iff.mpr (Set.mem_compl_singleton_iff.mp hx)).ne'
  rcases Nat.lt_or_ge n 3 with hn3 | hn3
  · interval_cases n
    · have heq : fundamentalSolution (n := 0) =
          fun (_ : EuclideanSpace ℝ (Fin 0)) => (0 : ℝ) := by
        funext; simp [fundamentalSolution]
      rw [heq]; exact contDiffOn_const
    · have heq : fundamentalSolution (n := 1) =
          fun x : EuclideanSpace ℝ (Fin 1) => (1 / 2 : ℝ) * ‖x‖ := by
        funext; simp [fundamentalSolution]
      rw [heq]; exact contDiffOn_const.mul hn_smooth
    · have heq : fundamentalSolution (n := 2) =
          fun x : EuclideanSpace ℝ (Fin 2) =>
            -(1 / (2 * Real.pi)) * Real.log ‖x‖ := by
        funext; simp [fundamentalSolution]
      rw [heq]
      exact contDiffOn_const.mul (hn_smooth.log hn_ne)
  · have heq : fundamentalSolution (n := n) = fun x : ℝⁿ =>
        (1 / ((n : ℝ) * ((n : ℝ) - 2) *
          (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal)) *
        ‖x‖ ^ (2 - (n : ℝ)) := by
      funext x
      simp only [fundamentalSolution, if_neg (show n ≠ 0 from by omega),
        if_neg (show n ≠ 1 from by omega), if_neg (show n ≠ 2 from by omega)]
    rw [heq]
    exact contDiffOn_const.mul (hn_smooth.rpow_const_of_ne hn_ne)

/-! #### Helpers for harmonicity of the fundamental solution

The real inner product as a bilinear CLM (`realInnerBiL`/`realInnerL`) and the radial-power
derivative/Laplacian formulas (`hasFDerivAt_norm_rpow_of_ne`, `laplacian_norm_rpow_eq`) live in
`Calculus.lean`, shared with the Heat chapter. -/

/-- Linearity of `Laplacian.laplacian` under scalar multiplication. -/
private lemma laplacian_const_mul (c : ℝ) (f : ℝⁿ → ℝ) (hf : ContDiffAt ℝ 2 f x) :
    Δ (fun y => c * f y) x = c * Δ f x := by
  have smul_eq : (fun y : ℝⁿ => c * f y) = c • f := funext fun y => (smul_eq_mul c (f y)).symm
  rw [smul_eq, InnerProductSpace.laplacian_smul c hf]
  simp [smul_eq_mul]

/-- **Laplacian of `log ‖·‖`**: `Δ(log ‖·‖)(x) = (n − 2) · ‖x‖^(−2)`. -/
private lemma laplacian_log_norm_eq (x : ℝⁿ) (hx : x ≠ 0) :
    Δ (fun x : ℝⁿ => Real.log ‖x‖) x = ((n : ℝ) - 2) * ‖x‖ ^ (-(2 : ℝ)) := by
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  rw [show Δ (fun y : ℝⁿ => Real.log ‖y‖) x =
        ∑ i, iteratedFDeriv ℝ 2 (fun y : ℝⁿ => Real.log ‖y‖) x ![e i, e i] from
      congr_fun (laplacian_eq_iteratedFDeriv_orthonormalBasis (fun y : ℝⁿ => Real.log ‖y‖) e) x]
  simp_rw [iteratedFDeriv_two_apply]
  -- fderiv of log ‖·‖ near x is ‖y‖^(-2) • realInnerL y
  have hfderiv : ∀ᶠ y in 𝓝 x,
      fderiv ℝ (fun y : ℝⁿ => Real.log ‖y‖) y = ‖y‖ ^ (-(2 : ℝ)) • realInnerL y := by
    filter_upwards [isOpen_compl_singleton.mem_nhds (Set.mem_compl_singleton_iff.mpr hx)]
    intro y hy
    have hyne : y ≠ 0 := Set.mem_compl_singleton_iff.mp hy
    have hynorm : 0 < ‖y‖ := norm_pos_iff.mpr hyne
    have hfn : HasFDerivAt (fun z : ℝⁿ => ‖z‖) (‖y‖ ^ (-(1 : ℝ)) • realInnerL y) y := by
      have := hasFDerivAt_norm_rpow_of_ne y hyne 1
      simp only [one_mul, show (1 : ℝ) - 2 = -(1 : ℝ) by norm_num, Real.rpow_one] at this
      exact this
    have hlog := hfn.log hynorm.ne'
    convert hlog.fderiv using 1
    rw [smul_smul]
    congr 1
    rw [show ‖y‖⁻¹ = ‖y‖ ^ (-(1 : ℝ)) by
          rw [Real.rpow_neg (norm_nonneg y), Real.rpow_one],
        ← Real.rpow_add hynorm]
    norm_num
  -- per-basis second derivative
  have hderiv2 : ∀ i : Fin n,
      fderiv ℝ (fderiv ℝ (fun y : ℝⁿ => Real.log ‖y‖)) x (e i) (e i) =
      -(2 : ℝ) * ‖x‖ ^ (-(4 : ℝ)) * ⟪x, e i⟫_ℝ ^ 2 + ‖x‖ ^ (-(2 : ℝ)) := by
    intro i
    have hfe : fderiv ℝ (fderiv ℝ (fun y : ℝⁿ => Real.log ‖y‖)) x =
        fderiv ℝ (fun y : ℝⁿ => ‖y‖ ^ (-(2 : ℝ)) • realInnerL y) x :=
      Filter.EventuallyEq.fderiv_eq hfderiv
    rw [hfe]
    have hc := hasFDerivAt_norm_rpow_of_ne x hx (-(2 : ℝ))
    have hcd : DifferentiableAt ℝ (fun y : ℝⁿ => ‖y‖ ^ (-(2 : ℝ))) x := hc.differentiableAt
    have hgd : DifferentiableAt ℝ (fun y : ℝⁿ => realInnerL y) x :=
      realInnerBiL.hasFDerivAt.differentiableAt
    have hconv : (fun y : ℝⁿ => ‖y‖ ^ (-(2 : ℝ)) • realInnerL y) =
        (fun y : ℝⁿ => ‖y‖ ^ (-(2 : ℝ))) • (fun y : ℝⁿ => realInnerL y) :=
      funext fun y => rfl
    rw [show fderiv ℝ (fun y : ℝⁿ => ‖y‖ ^ (-(2 : ℝ)) • realInnerL y) x =
        fderiv ℝ ((fun y : ℝⁿ => ‖y‖ ^ (-(2 : ℝ))) • fun y : ℝⁿ => realInnerL y) x from
      congr_arg (fderiv ℝ · x) hconv]
    rw [fderiv_smul hcd hgd]
    have hgfderiv : fderiv ℝ (fun y : ℝⁿ => realInnerL y) x = realInnerBiL :=
      realInnerBiL.hasFDerivAt.fderiv
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
              ContinuousLinearMap.smulRight_apply, hc.fderiv, hgfderiv]
    have hei : realInnerBiL (e i) (e i) = 1 := by
      have h := (orthonormal_iff_ite (𝕜 := ℝ)).mp
        (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal i i
      simp at h
      have heq : realInnerBiL (e i) (e i) = ⟪e i, e i⟫_ℝ := realInnerL_apply (e i) (e i)
      rw [heq]; simp only [e, EuclideanSpace.basisFun_apply]; exact h
    have hxi : realInnerL x (e i) = ⟪x, e i⟫_ℝ := realInnerL_apply x (e i)
    rw [hei, hxi]
    simp only [smul_eq_mul, mul_one]
    ring
  simp_rw [show ∀ i : Fin n, ![e i, e i] 0 = e i from fun i => rfl,
           show ∀ i : Fin n, ![e i, e i] 1 = e i from fun i => rfl]
  simp_rw [hderiv2]
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hparseval := e.sum_sq_inner_left x
  have hcombine : ‖x‖ ^ (-(4 : ℝ)) * ‖x‖ ^ 2 = ‖x‖ ^ (-(2 : ℝ)) := by
    rw [← Real.rpow_natCast ‖x‖ 2, ← Real.rpow_add hxpos]; congr 1; ring
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp_rw [← Finset.mul_sum]
  conv_lhs =>
    rw [show ∑ i : Fin n, ⟪x, e i⟫_ℝ ^ 2 = ‖x‖ ^ 2 from hparseval]
  conv_lhs =>
    rw [show -(2 : ℝ) * ‖x‖ ^ (-(4 : ℝ)) * ‖x‖ ^ 2 = -(2 : ℝ) * ‖x‖ ^ (-(2 : ℝ)) from by
      rw [show -(2 : ℝ) * ‖x‖ ^ (-(4 : ℝ)) * ‖x‖ ^ 2 =
          -(2 : ℝ) * (‖x‖ ^ (-(4 : ℝ)) * ‖x‖ ^ 2) from by ring]
      rw [hcombine]]
  ring

/-- **Key Lemma**: `fundamentalSolution` is harmonic on `ℝⁿ \ {0}`. -/
lemma fundamentalSolution_harmonic_off_zero (x : ℝⁿ) (hx : x ≠ 0) :
    Δ (fundamentalSolution : ℝⁿ → ℝ) x = 0 := by
  have hx_mem : x ∈ ({0} : Set ℝⁿ)ᶜ := Set.mem_compl_singleton_iff.mpr hx
  have hcd : ContDiffAt ℝ 2 (fundamentalSolution (n := n)) x :=
    (fundamentalSolution_contDiff_off_zero.contDiffAt
      (IsOpen.mem_nhds isOpen_compl_singleton hx_mem)).of_le le_top
  rcases Nat.lt_or_ge n 3 with hn3 | hn3
  · interval_cases n
    · have heq : (fundamentalSolution (n := 0) : EuclideanSpace ℝ (Fin 0) → ℝ) = fun _ => 0 :=
        funext (by simp [fundamentalSolution])
      rw [heq]; simp
    · have heq : (fundamentalSolution (n := 1) : EuclideanSpace ℝ (Fin 1) → ℝ) =
          fun x => (1 / 2 : ℝ) * ‖x‖ ^ (1 : ℝ) :=
        funext (by simp [fundamentalSolution, Real.rpow_one])
      have hf : ContDiffAt ℝ 2 (fun x : EuclideanSpace ℝ (Fin 1) => ‖x‖ ^ (1 : ℝ)) x := by
        simp_rw [Real.rpow_one]; exact (contDiffAt_norm ℝ hx).of_le le_top
      rw [heq, laplacian_const_mul (1/2) _ hf, laplacian_norm_rpow_eq 1 x hx]
      norm_num
    · have heq : (fundamentalSolution (n := 2) : EuclideanSpace ℝ (Fin 2) → ℝ) =
          fun x => -(1 / (2 * Real.pi)) * Real.log ‖x‖ :=
        funext (by simp [fundamentalSolution])
      have hf : ContDiffAt ℝ 2 (fun x : EuclideanSpace ℝ (Fin 2) => Real.log ‖x‖) x :=
        ((contDiffAt_norm ℝ hx).log (norm_ne_zero_iff.mpr hx)).of_le le_top
      rw [heq, laplacian_const_mul _ _ hf, laplacian_log_norm_eq x hx]
      norm_num
  · set c := (1 / ((n : ℝ) * ((n : ℝ) - 2) *
        (volume (Metric.ball (0 : ℝⁿ) 1)).toReal))
    have heq : (fundamentalSolution (n := n) : ℝⁿ → ℝ) = fun x => c * ‖x‖ ^ (2 - (n : ℝ)) :=
      funext (by simp [fundamentalSolution, c, show n ≠ 0 from by omega,
        show n ≠ 1 from by omega, show n ≠ 2 from by omega])
    have hf : ContDiffAt ℝ 2 (fun x : ℝⁿ => ‖x‖ ^ (2 - (n : ℝ))) x :=
      ((contDiffAt_norm ℝ hx).rpow_const_of_ne (norm_ne_zero_iff.mpr hx)).of_le le_top
    rw [heq, laplacian_const_mul c _ hf, laplacian_norm_rpow_eq (2 - (n:ℝ)) x hx]
    simp

/-! #### Helper lemmas for near-singularity integral -/

/-- Translation invariance of ball integrals:
    ∫_{B(x,ε)} f(x - y) dy = ∫_{B(0,ε)} f(z) dz.
    Proved via Set.indicator + integral_sub_left_eq_self. -/
private lemma integral_ball_translate (f : ℝⁿ → ℝ) (x : ℝⁿ) (ε : ℝ) :
    ∫ y in Metric.ball x ε, f (x - y) =
    ∫ z in Metric.ball (0 : ℝⁿ) ε, f z := by
  rw [← MeasureTheory.integral_indicator measurableSet_ball,
      ← MeasureTheory.integral_indicator measurableSet_ball]
  have h : (fun y : ℝⁿ => (Metric.ball x ε).indicator (fun y => f (x - y)) y) =
      (fun y : ℝⁿ => (Metric.ball (0 : ℝⁿ) ε).indicator f (x - y)) := by
    ext y
    unfold Set.indicator
    simp only [Metric.mem_ball, dist_eq_norm, norm_sub_rev, sub_zero]
  rw [h]
  exact MeasureTheory.integral_sub_left_eq_self
    ((Metric.ball (0 : ℝⁿ) ε).indicator f) MeasureTheory.volume x

/-- `‖Φ‖` is integrable on the unit ball `B(0,1)`. The radial profile of `‖Φ‖` is
    `r^(2−n)` (for `n ≥ 3`), `|log r|` (for `n = 2`), or linear/zero (small `n`); in every case
    the polar-coordinate integrand `r^(n−1)·‖Φ‖(r)` is bounded on `(0,1)`. We reduce to that
    one-dimensional integral with Mathlib's `n`-dim polar integration
    `integrable_fun_norm_addHaar` (filling the gap that earlier blocked this step). -/
lemma fundamentalSolution_norm_integrableOn_unitBall :
    MeasureTheory.IntegrableOn (fun y : ℝⁿ => ‖fundamentalSolution y‖) (Metric.ball 0 1) := by
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · -- `n = 0`: `Φ ≡ 0`.
    have hz : (fun y : ℝⁿ => ‖fundamentalSolution y‖) = fun _ => (0 : ℝ) := by
      funext y; simp [fundamentalSolution, hn0]
    rw [hz]; exact MeasureTheory.integrableOn_zero
  -- The radial profile `F` of `‖Φ‖`.
  set F : ℝ → ℝ := fun r =>
    if n = 1 then (1 / 2 : ℝ) * r
    else if n = 2 then |(-(1 / (2 * Real.pi)) * Real.log r)|
    else |(1 / ((n : ℝ) * ((n : ℝ) - 2) *
          (volume (Metric.ball (0 : ℝⁿ) 1)).toReal))| * r ^ (2 - (n : ℝ))
    with hFdef
  have hrad : (fun y : ℝⁿ => ‖fundamentalSolution y‖) = fun y => F ‖y‖ := by
    funext y
    simp only [fundamentalSolution, hFdef, if_neg (show n ≠ 0 by omega)]
    split_ifs with h1 h2
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    · rw [Real.norm_eq_abs]
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  -- Reduce the n-dim ball integral to the 1-D radial integral (shared `Calculus` lemma).
  rw [hrad]
  refine (integrableOn_unitBall_radial hnpos (f := F)).mpr ?_
  -- Now: `IntegrableOn (fun r => r^(n-1) * F r) (Ioo 0 1)`; split on `n`.
  rcases lt_or_ge n 3 with h3 | h3
  · interval_cases n
    · -- `n = 1`: the integrand is `(1/2)·r`, continuous.
      have hF1 : F = fun r : ℝ => (1 / 2 : ℝ) * r := by
        funext r; simp only [hFdef, if_true]
      simp only [hF1]
      exact ((by fun_prop : Continuous (fun r : ℝ => r ^ (1 - 1) * ((1 / 2 : ℝ) * r)))
        |>.integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
    · -- `n = 2`: the integrand is `(1/2π)·r·|log r| ≤ 1/2π`, bounded on a finite-measure set.
      have hF2 : F = fun r : ℝ => |(-(1 / (2 * Real.pi)) * Real.log r)| := by
        funext r; simp only [hFdef, if_true]; rw [if_neg (by decide : ¬(2 : ℕ) = 1)]
      simp only [hF2]
      have hgInt : MeasureTheory.IntegrableOn (fun _ : ℝ => 1 / (2 * Real.pi)) (Set.Ioo 0 1) :=
        MeasureTheory.integrableOn_const
          (hs := by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
      refine MeasureTheory.Integrable.mono' (g := fun _ => 1 / (2 * Real.pi)) hgInt ?_ ?_
      · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
        refine ContinuousOn.mul (by fun_prop) ?_
        refine continuous_abs.comp_continuousOn (continuousOn_const.mul ?_)
        exact Real.continuousOn_log.mono fun r hr => by
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact ne_of_gt hr.1
      · rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
        refine Filter.Eventually.of_forall fun r hr => ?_
        obtain ⟨hr0, hr1⟩ := hr
        simp only [Real.norm_eq_abs]
        have hlognn : Real.log r ≤ 0 := Real.log_nonpos hr0.le hr1.le
        have hlogle : r * -Real.log r ≤ 1 := by
          rw [← Real.log_inv]
          have hinv : Real.log r⁻¹ ≤ r⁻¹ - 1 := Real.log_le_sub_one_of_pos (by positivity)
          have hrr : r * (r⁻¹ - 1) = 1 - r := by
            rw [mul_sub, mul_inv_cancel₀ (ne_of_gt hr0), mul_one]
          calc r * Real.log r⁻¹ ≤ r * (r⁻¹ - 1) := mul_le_mul_of_nonneg_left hinv hr0.le
            _ = 1 - r := hrr
            _ ≤ 1 := by linarith
        have he : abs (r ^ (2 - 1) * abs (-(1 / (2 * Real.pi)) * Real.log r))
            = 1 / (2 * Real.pi) * (r * -Real.log r) := by
          rw [show r ^ (2 - 1) = r from by norm_num, abs_mul, abs_abs, abs_of_pos hr0,
            abs_mul, abs_neg, abs_of_pos (show (0 : ℝ) < 1 / (2 * Real.pi) by positivity),
            abs_of_nonpos hlognn]
          ring
        rw [he]
        calc 1 / (2 * Real.pi) * (r * -Real.log r)
            ≤ 1 / (2 * Real.pi) * 1 := mul_le_mul_of_nonneg_left hlogle (by positivity)
          _ = 1 / (2 * Real.pi) := by ring
  · -- `n ≥ 3`: the integrand simplifies to `|c|·r` (since `r^(n-1)·r^(2-n) = r`), continuous.
    have hpow : ∀ r : ℝ, 0 < r → r ^ (n - 1) * r ^ (2 - (n : ℝ)) = r := by
      intro r hr0
      rw [← Real.rpow_natCast r (n - 1), ← Real.rpow_add hr0,
        Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_one,
        show ((n : ℝ) - 1) + (2 - (n : ℝ)) = 1 by ring, Real.rpow_one]
    have hF3 : ∀ r : ℝ, 0 < r → r ^ (n - 1) * F r
        = |1 / ((n : ℝ) * ((n : ℝ) - 2) *
            (volume (Metric.ball (0 : ℝⁿ) 1)).toReal)| * r := by
      intro r hr0
      simp only [hFdef, if_neg (show n ≠ 1 by omega), if_neg (show n ≠ 2 by omega)]
      rw [show r ^ (n - 1) * (|1 / ((n : ℝ) * ((n : ℝ) - 2) *
              (volume (Metric.ball (0 : ℝⁿ) 1)).toReal)| * r ^ (2 - (n : ℝ)))
            = |1 / ((n : ℝ) * ((n : ℝ) - 2) *
              (volume (Metric.ball (0 : ℝⁿ) 1)).toReal)| * (r ^ (n - 1) * r ^ (2 - (n : ℝ)))
          from by ring, hpow r hr0]
    refine MeasureTheory.IntegrableOn.congr_fun
      (show MeasureTheory.IntegrableOn (fun r : ℝ => |1 / ((n : ℝ) * ((n : ℝ) - 2) *
          (volume (Metric.ball (0 : ℝⁿ) 1)).toReal)| * r) (Set.Ioo 0 1) from
        ((continuous_const.mul continuous_id).integrableOn_Icc).mono_set
          Set.Ioo_subset_Icc_self)
      ?_ measurableSet_Ioo
    intro r hr
    exact (hF3 r hr.1).symm

/-- Near-singularity integral vanishes as ε → 0 (Evans §2.2.4, p.23).
    ∫_{B(x,ε)} ‖Φ(x-y)‖ dy → 0 as ε → 0⁺.

    Proof strategy:
    1. Translate: ∫_{B(x,ε)} ‖Φ(x-y)‖ = ∫_{B(0,ε)} ‖Φ‖ via integral_ball_translate.
    2. ‖Φ‖ integrable on B(0,1): `fundamentalSolution_norm_integrableOn_unitBall`, proved via
       Mathlib's n-dim polar integration (∫_{B(0,1)} ‖y‖^(2-n) = nωₙ ∫₀¹ r dr < ∞).
    3. Sequential convergence: B(0,1/(k+1)) ↘ {0}, use tendsto_setIntegral_of_antitone.
    4. Transfer: sequential → nhdsWithin via Metric.tendsto_nhdsWithin_nhds. -/
lemma fundamentalSolution_near_integral_tendsto_zero (x : ℝⁿ) :
    Filter.Tendsto
      (fun ε => ∫ y in Metric.ball x ε, ‖fundamentalSolution (x - y)‖)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0) := by
  have hshift : ∀ ε : ℝ, ∫ y in Metric.ball x ε, ‖fundamentalSolution (x - y)‖ =
      ∫ z in Metric.ball (0 : ℝⁿ) ε, ‖fundamentalSolution z‖ :=
    fun ε => integral_ball_translate (fun z => ‖fundamentalSolution z‖) x ε
  simp_rw [hshift]
  -- Step 2: ‖Φ‖ is locally integrable on B(0, 1), via n-dim polar integration
  -- (Mathlib's `integrable_fun_norm_addHaar`).
  have hint : MeasureTheory.IntegrableOn (fun y : ℝⁿ => ‖fundamentalSolution y‖)
      (Metric.ball 0 1) := fundamentalSolution_norm_integrableOn_unitBall
  -- Step 3: sequential convergence via antitone balls B(0, 1/(k+1)) → {0}
  have hinter : ⋂ k : ℕ, Metric.ball (0 : ℝⁿ) (1 / ((k : ℝ) + 1)) = {0} := by
    ext y; simp only [Set.mem_iInter, Metric.mem_ball, dist_zero_right, Set.mem_singleton_iff]
    constructor
    · intro h
      rw [← norm_eq_zero]; apply le_antisymm _ (norm_nonneg _)
      apply le_of_forall_pos_le_add; intro ε hε
      obtain ⟨k, hk⟩ := exists_nat_gt (1 / ε)
      have hle : ‖y‖ ≤ 1 / ((k : ℝ) + 1) := le_of_lt (h k)
      have hlt : 1 / ((k : ℝ) + 1) ≤ ε := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) + 1)]
        have := (div_lt_iff₀ hε).mp hk
        nlinarith [Nat.cast_nonneg (α := ℝ) k]
      linarith
    · rintro rfl k
      simp only [norm_zero]
      positivity
  have hseq : Filter.Tendsto
      (fun k : ℕ => ∫ z in Metric.ball (0 : ℝⁿ) (1 / ((k : ℝ) + 1)), ‖fundamentalSolution z‖)
      Filter.atTop (nhds 0) := by
    -- ∫_{B(0,1/(k+1))} ‖Φ‖ → ∫_{{0}} ‖Φ‖ = 0
    -- {0} integral vanishes: n=0 by fundamentalSolution=0; n≥1 by volume {0} = 0 (NoAtoms).
    have hfin : ∫ z in ({0} : Set ℝⁿ), ‖fundamentalSolution z‖ = 0 := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [fundamentalSolution]
      · rw [MeasureTheory.integral_singleton]
        have h0 : (MeasureTheory.volume : MeasureTheory.Measure ℝⁿ) {0} = 0 := by
          haveI : Nontrivial ℝⁿ :=
            ⟨0, EuclideanSpace.single ⟨0, hn⟩ 1, by
              intro h
              have : (EuclideanSpace.single ⟨0, hn⟩ (1:ℝ) : Fin n → ℝ) ⟨0, hn⟩ = 0 := by
                rw [← h]; simp
              simp at this⟩
          haveI : (𝓝[≠] (0 : ℝⁿ)).NeBot := Real.punctured_nhds_module_neBot 0
          haveI : MeasureTheory.NoAtoms (MeasureTheory.volume : MeasureTheory.Measure ℝⁿ) :=
            MeasureTheory.Measure.IsAddHaarMeasure.noAtoms _
          exact MeasureTheory.NoAtoms.measure_singleton 0
        simp [MeasureTheory.Measure.real, h0]
    rw [← hfin, ← hinter]
    apply MeasureTheory.tendsto_setIntegral_of_antitone
    · intro k; exact measurableSet_ball
    · intro a b hab
      exact Metric.ball_subset_ball (by
        apply div_le_div_of_nonneg_left one_pos.le (by positivity) (by
          exact_mod_cast Nat.add_le_add_right hab 1))
    · exact ⟨0, hint.mono (Metric.ball_subset_ball (by norm_cast; norm_num)) le_rfl⟩
  -- Step 4: transfer sequential → nhdsWithin 0 (Ioi 0)
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro δ hδ
  obtain ⟨k, hk⟩ := Metric.tendsto_atTop.mp hseq δ hδ
  refine ⟨1 / ((k : ℝ) + 1), by positivity, fun ε hεpos hεδ => ?_⟩
  have hεpos' : 0 < ε := Set.mem_Ioi.mp hεpos
  have hεlt : ε < 1 / ((k : ℝ) + 1) := by
    simp only [Real.dist_eq, sub_zero, abs_of_pos hεpos'] at hεδ; exact hεδ
  have hint_k : MeasureTheory.IntegrableOn (fun y : ℝⁿ => ‖fundamentalSolution y‖)
      (Metric.ball 0 (1 / ((k : ℝ) + 1))) :=
    hint.mono (Metric.ball_subset_ball (by
      rw [div_le_one (by positivity : (0 : ℝ) < (k : ℝ) + 1)]
      linarith [Nat.cast_nonneg (α := ℝ) k])) le_rfl
  have hball_sub : Metric.ball (0 : ℝⁿ) ε ⊆ Metric.ball (0 : ℝⁿ) (1 / ((k : ℝ) + 1)) :=
    Metric.ball_subset_ball hεlt.le
  have hmono : ∫ z in Metric.ball (0 : ℝⁿ) ε, ‖fundamentalSolution z‖ ≤
      ∫ z in Metric.ball (0 : ℝⁿ) (1 / ((k : ℝ) + 1)), ‖fundamentalSolution z‖ := by
    apply MeasureTheory.setIntegral_mono_set hint_k
    · exact Filter.Eventually.of_forall (fun z =>
        show (0 : ℝ) ≤ ‖fundamentalSolution z‖ from norm_nonneg _)
    · exact MeasureTheory.ae_of_all _ (fun z hz => hball_sub hz)
  have hkle := hk k le_rfl
  have hk_nn : 0 ≤ ∫ z in Metric.ball (0 : ℝⁿ) (1 / ((k : ℝ) + 1)),
      ‖fundamentalSolution z‖ :=
    MeasureTheory.integral_nonneg (fun z => norm_nonneg (fundamentalSolution z))
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hk_nn] at hkle
  have hint_nn : 0 ≤ ∫ z in Metric.ball (0 : ℝⁿ) ε, ‖fundamentalSolution z‖ :=
    MeasureTheory.integral_nonneg (fun z => norm_nonneg _)
  simp only [Real.dist_eq, sub_zero, abs_of_nonneg hint_nn]
  linarith

/-- **Green's second identity** on annular domain `B(x,r) \ B(x,ε)`.
    Evans §2.2.4 strategy:
    (1) Algebra:  v Δu − u Δv = div(v ∇u − u ∇v)      [product rule, cross terms cancel]
    (2) Gauss–Green on annulus: ∫_Ω div F = ∫_{S_r} F·ν dσ − ∫_{S_ε} F·ν dσ
        Sign: annulus outward normal on inner sphere is −ν (inward to B(x,ε)).
    Blocked: step (2) needs Stokes on smooth domains, not yet in Mathlib.
    (Mathlib's divergence theorem covers rectangular boxes only.) -/
lemma green_identity_annulus (u v : ℝⁿ → ℝ) (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (x : ℝⁿ) (r ε : ℝ) (hr : 0 < r) (hε : 0 < ε) (hεr : ε < r) :
    ∫ y in Metric.ball x r \ Metric.ball x ε, (v y * Δ u y - u y * Δ v y)
    = (∫ y in Metric.sphere x r,
        (v y * ⟪gradient u y, ‖y - x‖⁻¹ • (y - x)⟫_ℝ -
         u y * ⟪gradient v y, ‖y - x‖⁻¹ • (y - x)⟫_ℝ)
        ∂(Measure.hausdorffMeasure ((n : ℝ) - 1)))
    - (∫ y in Metric.sphere x ε,
        (v y * ⟪gradient u y, ‖y - x‖⁻¹ • (y - x)⟫_ℝ -
         u y * ⟪gradient v y, ‖y - x‖⁻¹ • (y - x)⟫_ℝ)
        ∂(Measure.hausdorffMeasure ((n : ℝ) - 1))) := by
  -- Standard ONB for ℝⁿ
  set e := EuclideanSpace.basisFun (Fin n) ℝ with he_def
  -- Step 1 (Evans §2.2, algebra): v Δu − u Δv = ∑ᵢ ∂_{eᵢ}(v·∂_{eᵢ}u − u·∂_{eᵢ}v)
  -- Proof: product rule gives ∂_{eᵢ}(v·∂_{eᵢ}u) = (∂_{eᵢ}v)(∂_{eᵢ}u) + v·∂²_{eᵢeᵢ}u,
  -- and the cross terms (∂_{eᵢ}v)(∂_{eᵢ}u) cancel when we subtract the same with u↔v.
  have hdivid : ∀ y : ℝⁿ,
      v y * Δ u y - u y * Δ v y =
      ∑ i : Fin n, fderiv ℝ (fun z =>
          v z * fderiv ℝ u z (e i) - u z * fderiv ℝ v z (e i)) y (e i) := by
    intro y
    -- Expand Δu, Δv using the ONB: Δf y = ∑ᵢ iteratedFDeriv 2 f y ![eᵢ, eᵢ]
    have hΔu : Δ u y = ∑ i : Fin n, iteratedFDeriv ℝ 2 u y ![e i, e i] :=
      congr_fun (laplacian_eq_iteratedFDeriv_orthonormalBasis u e) y
    have hΔv : Δ v y = ∑ i : Fin n, iteratedFDeriv ℝ 2 v y ![e i, e i] :=
      congr_fun (laplacian_eq_iteratedFDeriv_orthonormalBasis v e) y
    rw [hΔu, hΔv]
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    congr 1; ext i; symm
    -- For each i: compute fderiv via product rule and chain rule
    -- HasFDerivAt for fun z => fderiv u z (eᵢ):
    --   fderiv u is C¹ (from hu : ContDiff 2 u), evaluate the CLM at eᵢ for chain rule.
    have hfdu_i : HasFDerivAt (fun z : ℝⁿ => fderiv ℝ u z (e i))
        ((fderiv ℝ (fderiv ℝ u) y).flip (e i)) y := by
      have h1 : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
      have h2 : HasFDerivAt (fderiv ℝ u) (fderiv ℝ (fderiv ℝ u) y) y :=
        (h1.differentiable (by norm_num)).differentiableAt.hasFDerivAt
      have h3 := h2.clm_apply (hasFDerivAt_const (e i) y)
      simp only [ContinuousLinearMap.comp_zero, zero_add] at h3
      exact h3
    have hfdv_i : HasFDerivAt (fun z : ℝⁿ => fderiv ℝ v z (e i))
        ((fderiv ℝ (fderiv ℝ v) y).flip (e i)) y := by
      have h1 : ContDiff ℝ 1 (fderiv ℝ v) := hv.fderiv_right (by norm_num)
      have h2 : HasFDerivAt (fderiv ℝ v) (fderiv ℝ (fderiv ℝ v) y) y :=
        (h1.differentiable (by norm_num)).differentiableAt.hasFDerivAt
      have h3 := h2.clm_apply (hasFDerivAt_const (e i) y)
      simp only [ContinuousLinearMap.comp_zero, zero_add] at h3
      exact h3
    -- HasFDerivAt for v and u themselves
    have hv_hfd : HasFDerivAt v (fderiv ℝ v y) y :=
      (hv.differentiable (by norm_num)).differentiableAt.hasFDerivAt
    have hu_hfd : HasFDerivAt u (fderiv ℝ u y) y :=
      (hu.differentiable (by norm_num)).differentiableAt.hasFDerivAt
    -- Product rule + subtraction: first term v*(fderiv u · eᵢ), second u*(fderiv v · eᵢ)
    have hterm : HasFDerivAt (fun z : ℝⁿ => v z * fderiv ℝ u z (e i) - u z * fderiv ℝ v z (e i))
        (v y • (fderiv ℝ (fderiv ℝ u) y).flip (e i) + fderiv ℝ u y (e i) • fderiv ℝ v y -
         (u y • (fderiv ℝ (fderiv ℝ v) y).flip (e i) + fderiv ℝ v y (e i) • fderiv ℝ u y)) y :=
      (hv_hfd.mul hfdu_i).sub (hu_hfd.mul hfdv_i)
    -- Evaluate at eᵢ and use iteratedFDeriv_two_apply to identify ∂²u
    rw [hterm.fderiv]
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
               ContinuousLinearMap.smul_apply, ContinuousLinearMap.flip_apply, smul_eq_mul]
    -- iteratedFDeriv_two_apply: fderiv(fderiv u) y (eᵢ) (eᵢ) = iteratedFDeriv 2 u y ![eᵢ,eᵢ]
    have hd2u : fderiv ℝ (fderiv ℝ u) y (e i) (e i) = iteratedFDeriv ℝ 2 u y ![e i, e i] := by
      have h := iteratedFDeriv_two_apply (𝕜 := ℝ) u y ![e i, e i]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
      exact h.symm
    have hd2v : fderiv ℝ (fderiv ℝ v) y (e i) (e i) = iteratedFDeriv ℝ 2 v y ![e i, e i] := by
      have h := iteratedFDeriv_two_apply (𝕜 := ℝ) v y ![e i, e i]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
      exact h.symm
    rw [hd2u, hd2v]; ring
  -- Step 2 (Evans §2.2): Gauss–Green theorem on the annulus Ω = B(x,r) \ B̄(x,ε).
  --   ∫_Ω ∑ᵢ ∂_{eᵢ} Fᵢ = ∫_{S(x,r)} ∑ᵢ Fᵢ ⟨eᵢ, ν⟩ dσ − ∫_{S(x,ε)} ∑ᵢ Fᵢ ⟨eᵢ, ν⟩ dσ
  -- where Fᵢ(y) = v(y)·∂_{eᵢ}u(y) − u(y)·∂_{eᵢ}v(y) and ν = ‖y−x‖⁻¹(y−x).
  -- Inner product expansion: ∑ᵢ Fᵢ ⟨eᵢ, ν⟩ = ∑ᵢ(v·∂_{eᵢ}u − u·∂_{eᵢ}v)⟨eᵢ,ν⟩
  --   = v·⟨∇u, ν⟩ − u·⟨∇v, ν⟩  (linearity + ⟨∇f, w⟩ = fderiv f · w = ∑ᵢ ∂_{eᵢ}f · ⟨eᵢ,w⟩).
  -- BLOCKED: Stokes/Gauss-Green on smooth domains is not in Mathlib.
  sorry

/-- Total outward normal flux of `∇Φ` through `∂B(0, ε)` equals `−1`. -/
lemma fundamentalSolution_totalFlux (ε : ℝ) (hε : 0 < ε) :
    ∫ y in Metric.sphere (0 : ℝⁿ) ε,
      ⟪gradient fundamentalSolution y, ‖y‖⁻¹ • y⟫_ℝ
      ∂(Measure.hausdorffMeasure ((n : ℝ) - 1)) = -1 := by
  sorry

/-- Boundary integral from Green's identity converges to `f(x)` as ε → 0. -/
lemma green_boundary_tendsto_f (f : ℝⁿ → ℝ) (hf : ContDiff ℝ 2 f)
    (hf_supp : HasCompactSupport f) (x : ℝⁿ) :
    Filter.Tendsto
      (fun ε => ∫ y in Metric.sphere x ε,
        (fundamentalSolution (y - x) * ⟪gradient f y, ‖y - x‖⁻¹ • (y - x)⟫_ℝ
         - f y * ⟪gradient fundamentalSolution (y - x), ‖y - x‖⁻¹ • (y - x)⟫_ℝ)
        ∂(Measure.hausdorffMeasure ((n : ℝ) - 1)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (f x)) := by
  sorry

/-- **Representation Formula** (Evans §2.2.4, Theorem 9).
    u(x) = ∫ Φ(x-y) f(y) dy solves −Δu = f.
    Proof requires: green_identity_annulus + fundamentalSolution_totalFlux
    + fundamentalSolution_near_integral_tendsto_zero + green_boundary_tendsto_f. -/
theorem newtonianPotential_solves_poisson (f : ℝⁿ → ℝ) (hf : ContDiff ℝ 2 f)
    (hf_supp : HasCompactSupport f) :
    IsPoissonSolution Set.univ f (newtonianPotential f) := by
  intro x _
  sorry

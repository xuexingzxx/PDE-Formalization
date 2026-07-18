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

/-! ### Toward the ball mean-value property

The ball version does not need a coarea formula: the divergence theorem on the unit ball applied to
the field `V(z) = u(x+r•z)•z` yields the ODE `ρ·g'(ρ) + (m+2)·g(ρ) = (m+2)·vol(B₁)·u(x)` for
`g(ρ) = ∫_{B₁} u(x+ρz)`, whose integrating factor `ρ^{m+2}` gives
`∫_{B(x,r)} u = vol(B(x,r))·u(x)`. -/

/-- Divergence of the identity field is the dimension. -/
lemma divergenceE_id (z : ℝ^(m + 2)) : divergenceE (fun y : ℝ^(m + 2) => y) z = (m + 2 : ℝ) := by
  simp only [divergenceE, fderiv_id']
  simp

/-- Gradient chain rule under the affine map `z ↦ x + r • z`. -/
lemma grad_chain (x : ℝ^(m + 2)) (r : ℝ) (u : (ℝ^(m + 2)) → ℝ)
    (hu : ∀ y, DifferentiableAt ℝ u y) (z : ℝ^(m + 2)) :
    gradient (fun z => u (x + r • z)) z = r • gradient u (x + r • z) := by
  have hcomp : HasFDerivAt (fun z => u (x + r • z))
      ((fderiv ℝ u (x + r • z)).comp ((r : ℝ) • ContinuousLinearMap.id ℝ (ℝ^(m + 2)))) z := by
    have haff : HasFDerivAt (fun z : ℝ^(m + 2) => x + r • z)
        ((r : ℝ) • ContinuousLinearMap.id ℝ (ℝ^(m + 2))) z :=
      ((hasFDerivAt_id z).const_smul r).const_add x
    exact (hu (x + r • z)).hasFDerivAt.comp z haff
  have hd : DifferentiableAt ℝ (fun z => u (x + r • z)) z := hcomp.differentiableAt
  ext i
  rw [gradient_ofLp hd i, hcomp.fderiv]
  simp only [WithLp.ofLp_smul, Pi.smul_apply, gradient_ofLp (hu (x + r • z)) i,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    map_smul, smul_eq_mul]

/-- Divergence of the field `V(z) = u(x + r•z) • z`. -/
lemma div_ball_field (x : ℝ^(m + 2)) (r : ℝ) (u : (ℝ^(m + 2)) → ℝ) (hu : ContDiff ℝ 2 u)
    (z : ℝ^(m + 2)) :
    divergenceE (fun z => u (x + r • z) • z) z
      = r * ⟪gradient u (x + r • z), z⟫ + (m + 2) * u (x + r • z) := by
  have hw : DifferentiableAt ℝ (fun z => u (x + r • z)) z :=
    (hu.differentiable (by norm_num)).differentiableAt.comp z (by fun_prop)
  rw [divergenceE_smul (fun z => u (x + r • z)) (fun y => y) z hw differentiableAt_id,
    divergenceE_id, grad_chain x r u (fun y => (hu.differentiable (by norm_num)).differentiableAt) z,
    real_inner_smul_left]
  ring

/-- Differentiation under the integral over the fixed unit ball:
`d/ds ∫_{B(0,1)} u(x+s•z) dz = ∫_{B(0,1)} ⟪∇u(x+s•z), z⟫ dz`. -/
lemma hasDerivAt_ball_integral (x : ℝ^(m + 2)) (u : (ℝ^(m + 2)) → ℝ) (hu : ContDiff ℝ 2 u)
    (s₀ : ℝ) :
    HasDerivAt (fun s => ∫ z in Metric.ball (0 : ℝ^(m + 2)) 1, u (x + s • z))
      (∫ z in Metric.ball (0 : ℝ^(m + 2)) 1, ⟪gradient u (x + s₀ • z), z⟫) s₀ := by
  set μ := (volume : Measure (ℝ^(m + 2))).restrict (Metric.ball (0 : ℝ^(m + 2)) 1) with hμ
  haveI : IsFiniteMeasure μ :=
    ⟨by rw [hμ, Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  set K : Set (ℝ^(m + 2)) := (fun p : ℝ × (ℝ^(m + 2)) => x + p.1 • p.2)
    '' (Set.Icc (s₀ - 1) (s₀ + 1) ×ˢ Metric.closedBall (0 : ℝ^(m + 2)) 1) with hK
  have hKc : IsCompact K :=
    (isCompact_Icc.prod (isCompact_closedBall (0 : ℝ^(m + 2)) 1)).image
      (continuous_const.add (continuous_fst.smul continuous_snd))
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn (contDiff_gradient hu).continuous.continuousOn
  have hmemK : ∀ s ∈ Metric.ball s₀ 1, ∀ z ∈ Metric.ball (0 : ℝ^(m + 2)) 1, x + s • z ∈ K := by
    intro s hs z hz
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hs
    exact ⟨(s, z), ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩, Metric.ball_subset_closedBall hz⟩, rfl⟩
  have hcont₀ : Continuous (fun z : ℝ^(m + 2) => u (x + s₀ • z)) :=
    hu.continuous.comp (continuous_const.add (continuous_const.smul continuous_id))
  have hdiff : ∀ z : ℝ^(m + 2), ∀ s : ℝ,
      HasDerivAt (fun s => u (x + s • z)) (⟪gradient u (x + s • z), z⟫) s := by
    intro z s
    have hline : HasDerivAt (fun t : ℝ => x + t • z) z s := by
      simpa using ((hasDerivAt_id (x := s)).smul_const z).const_add x
    have hcomp := (hu.differentiable (by norm_num) (x + s • z)).hasFDerivAt.comp_hasDerivAt s hline
    rwa [inner_gradient_left (hu.differentiable (by norm_num) _)]
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun _ => C)
    (F := fun s z => u (x + s • z)) (F' := fun s z => ⟪gradient u (x + s • z), z⟫)
    (Metric.ball_mem_nhds s₀ one_pos) ?_ ?_ ?_ ?_ (integrable_const C) ?_).2
  · refine Filter.Eventually.of_forall (fun s => ?_)
    exact (hu.continuous.comp
      (continuous_const.add (continuous_const.smul continuous_id))).aestronglyMeasurable
  · obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℝ^(m + 2)) 1).exists_bound_of_continuousOn
      hcont₀.continuousOn
    refine (integrable_const M).mono' hcont₀.aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_ball (fun z hz => ?_))
    exact hM z (Metric.ball_subset_closedBall hz)
  · have hcont : Continuous (fun z : ℝ^(m + 2) => ⟪gradient u (x + s₀ • z), z⟫) :=
      ((contDiff_gradient hu).continuous.comp
        (continuous_const.add (continuous_const.smul continuous_id))).inner continuous_id
    exact hcont.aestronglyMeasurable
  · refine (ae_restrict_of_forall_mem measurableSet_ball (fun z hz => ?_))
    intro s hs
    have hz1 : ‖z‖ ≤ 1 := by rw [Metric.mem_ball, dist_zero_right] at hz; exact hz.le
    calc ‖(⟪gradient u (x + s • z), z⟫ : ℝ)‖ ≤ ‖gradient u (x + s • z)‖ * ‖z‖ :=
          norm_inner_le_norm _ _
      _ ≤ C := by
          have hg : ‖gradient u (x + s • z)‖ ≤ C := hC _ (hmemK s hs z hz)
          nlinarith [norm_nonneg (gradient u (x + s • z)), norm_nonneg z]
  · exact Filter.Eventually.of_forall (fun z s _ => hdiff z s)

/-- The ODE relation from the divergence theorem: for `0 < ρ ≤ r`,
`ρ·h(ρ) + (m+2)·g(ρ) = (m+2)·vol(B₁)·u(x)` where `g(ρ)=∫_{B₁}u(x+ρz)`, `h(ρ)=∫_{B₁}⟪∇u(x+ρz),z⟫`. -/
lemma ball_ode (x : ℝ^(m + 2)) (r : ℝ) (u : (ℝ^(m + 2)) → ℝ) (hu : ContDiff ℝ 2 u)
    (hΔ : ∀ y ∈ Metric.closedBall x r, Laplacian.laplacian u y = 0)
    {ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ r) :
    ρ * (∫ z in Metric.ball (0 : ℝ^(m + 2)) 1, ⟪gradient u (x + ρ • z), z⟫)
      + ((m : ℝ) + 2) * (∫ z in Metric.ball (0 : ℝ^(m + 2)) 1, u (x + ρ • z))
      = ((m : ℝ) + 2) * (volume (Metric.ball (0 : ℝ^(m + 2)) 1)).toReal * u x := by
  have haff : Continuous (fun z : ℝ^(m + 2) => x + ρ • z) :=
    continuous_const.add (continuous_const.smul continuous_id)
  have hVcd : ContDiff ℝ 1 (fun z : ℝ^(m + 2) => u (x + ρ • z) • z) := by
    have h1 : ContDiff ℝ 1 (fun z : ℝ^(m + 2) => u (x + ρ • z)) :=
      (hu.of_le (by norm_num)).comp (by fun_prop)
    exact h1.smul contDiff_id
  have hdiv := divergence_theorem (isBoundedC1Domain_ball (0 : ℝ^(m + 2)) 1 one_pos)
    (isOutwardNormal_ball (0 : ℝ^(m + 2)) 1 one_pos) hVcd
  rw [frontier_ball (0 : ℝ^(m + 2)) one_ne_zero] at hdiv
  have hc1 : Continuous (fun z : ℝ^(m + 2) => (⟪gradient u (x + ρ • z), z⟫ : ℝ)) :=
    ((contDiff_gradient hu).continuous.comp haff).inner continuous_id
  have hc2 : Continuous (fun z : ℝ^(m + 2) => u (x + ρ • z)) := hu.continuous.comp haff
  have hint1 : IntegrableOn (fun z : ℝ^(m + 2) => (⟪gradient u (x + ρ • z), z⟫ : ℝ))
      (Metric.ball (0 : ℝ^(m + 2)) 1) :=
    (hc1.continuousOn.integrableOn_compact (isCompact_closedBall 0 1)).mono_set
      Metric.ball_subset_closedBall
  have hint2 : IntegrableOn (fun z : ℝ^(m + 2) => u (x + ρ • z))
      (Metric.ball (0 : ℝ^(m + 2)) 1) :=
    (hc2.continuousOn.integrableOn_compact (isCompact_closedBall 0 1)).mono_set
      Metric.ball_subset_closedBall
  rw [setIntegral_congr_fun measurableSet_ball (fun z _ => div_ball_field x ρ u hu z),
    integral_add (hint1.const_mul ρ) (hint2.const_mul _), integral_const_mul,
    integral_const_mul] at hdiv
  have hfluxeq : ∫ z in Metric.sphere (0 : ℝ^(m + 2)) 1,
        (⟪u (x + ρ • z) • z, (1 : ℝ)⁻¹ • (z - (0 : ℝ^(m + 2)))⟫ : ℝ)
        ∂(μHE[m + 1] : Measure (ℝ^(m + 2)))
      = ∫ z in Metric.sphere (0 : ℝ^(m + 2)) 1, u (x + ρ • z)
        ∂(μHE[m + 1] : Measure (ℝ^(m + 2))) := by
    refine setIntegral_congr_fun Metric.isClosed_sphere.measurableSet (fun z hz => ?_)
    rw [Metric.mem_sphere, dist_zero_right] at hz
    rw [inv_one, sub_zero, one_smul, real_inner_smul_left, real_inner_self_eq_norm_sq, hz]
    ring
  rw [hfluxeq] at hdiv
  have hmean : ⨍ z in Metric.sphere (0 : ℝ^(m + 2)) 1, u (x + ρ • z)
      ∂(μHE[m + 1] : Measure (ℝ^(m + 2))) = u x := by
    rw [← setAverage_sphere_rescale x hρ u]
    exact (harmonic_sphereMean_μHE x ρ hρ u hu
      (fun y hy => hΔ y (Metric.closedBall_subset_closedBall hρr hy))).symm
  have hsm : (μHE[m + 1] (Metric.sphere (0 : ℝ^(m + 2)) 1)).toReal
      = ((m : ℝ) + 2) * (volume (Metric.ball (0 : ℝ^(m + 2)) 1)).toReal := by
    rw [sphere_surfaceMeasure (0 : ℝ^(m + 2)) 1 one_pos]; ring
  rw [setAverage_eq, measureReal_def, smul_eq_mul] at hmean
  have hflux : ∫ z in Metric.sphere (0 : ℝ^(m + 2)) 1, u (x + ρ • z)
      ∂(μHE[m + 1] : Measure (ℝ^(m + 2)))
      = ((m : ℝ) + 2) * (volume (Metric.ball (0 : ℝ^(m + 2)) 1)).toReal * u x := by
    have h1 : ∫ z in Metric.sphere (0 : ℝ^(m + 2)) 1, u (x + ρ • z)
        ∂(μHE[m + 1] : Measure (ℝ^(m + 2)))
        = (μHE[m + 1] (Metric.sphere (0 : ℝ^(m + 2)) 1)).toReal * u x := by
      rw [← hmean, ← mul_assoc, mul_inv_cancel₀ sphere_surfaceMeasure_pos.ne', one_mul]
    rw [h1, hsm]
  rw [hflux] at hdiv
  linarith [hdiv]

/-- Affine change of variables for the ball integral: `∫_{B(x,r)} u = rⁿ·∫_{B(0,1)} u(x+r•z)`. -/
lemma ball_scaling (x : ℝ^(m + 2)) (r : ℝ) (hr : 0 < r) (u : (ℝ^(m + 2)) → ℝ) :
    ∫ y in Metric.ball x r, u y
      = r ^ (m + 2) * ∫ z in Metric.ball (0 : ℝ^(m + 2)) 1, u (x + r • z) := by
  have h1 := Measure.setIntegral_comp_smul_of_pos (μ := (volume : Measure (ℝ^(m + 2))))
    (fun w => u (x + w)) (Metric.ball (0 : ℝ^(m + 2)) 1) hr
  rw [finrank_euclideanSpace_fin, smul_unitBall_of_pos hr] at h1
  have hpre : (fun w : ℝ^(m + 2) => x + w) ⁻¹' (Metric.ball x r) = Metric.ball (0 : ℝ^(m + 2)) r := by
    ext w; simp [Metric.mem_ball, dist_eq_norm]
  have htrans : ∫ w in Metric.ball (0 : ℝ^(m + 2)) r, u (x + w) = ∫ y in Metric.ball x r, u y := by
    rw [← hpre]
    exact (measurePreserving_add_left volume x).setIntegral_preimage_emb
      (measurableEmbedding_addLeft x) u (Metric.ball x r)
  rw [h1, htrans, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ (by positivity : (r : ℝ) ^ (m + 2) ≠ 0), one_mul]

/-- **Ball integral of a harmonic function**: `∫_{B(x,r)} u = vol(B(x,r))·u(x)`. -/
lemma ball_integral_eq (x : ℝ^(m + 2)) (r : ℝ) (hr : 0 < r) (u : (ℝ^(m + 2)) → ℝ)
    (hu : ContDiff ℝ 2 u)
    (hΔ : ∀ y ∈ Metric.closedBall x r, Laplacian.laplacian u y = 0) :
    ∫ y in Metric.ball x r, u y = (volume (Metric.ball x r)).toReal * u x := by
  set g : ℝ → ℝ := fun ρ => ∫ z in Metric.ball (0 : ℝ^(m + 2)) 1, u (x + ρ • z) with hgdef
  set h : ℝ → ℝ := fun ρ => ∫ z in Metric.ball (0 : ℝ^(m + 2)) 1, ⟪gradient u (x + ρ • z), z⟫
    with hhdef
  have hg' : ∀ ρ, HasDerivAt g (h ρ) ρ := fun ρ => hasDerivAt_ball_integral x u hu ρ
  set vol1 := (volume (Metric.ball (0 : ℝ^(m + 2)) 1)).toReal with hvol1
  set P : ℝ → ℝ := fun ρ => ρ ^ (m + 2) * g ρ with hPdef
  set Q : ℝ → ℝ := fun ρ => vol1 * u x * ρ ^ (m + 2) with hQdef
  have hpow : ∀ ρ : ℝ, HasDerivAt (fun ρ : ℝ => ρ ^ (m + 2)) (((m : ℝ) + 2) * ρ ^ (m + 1)) ρ := by
    intro ρ; simpa using hasDerivAt_pow (m + 2) ρ
  have hD0 : ∀ ρ ∈ Set.uIcc (0 : ℝ) r, HasDerivAt (fun ρ => P ρ - Q ρ) 0 ρ := by
    intro ρ hρ
    rw [Set.uIcc_of_le hr.le] at hρ
    have hdP : HasDerivAt P (((m : ℝ) + 2) * ρ ^ (m + 1) * g ρ + ρ ^ (m + 2) * h ρ) ρ :=
      (hpow ρ).mul (hg' ρ)
    have hdQ : HasDerivAt Q (vol1 * u x * (((m : ℝ) + 2) * ρ ^ (m + 1))) ρ :=
      (hpow ρ).const_mul (vol1 * u x)
    have hd := hdP.sub hdQ
    have hval : ((m : ℝ) + 2) * ρ ^ (m + 1) * g ρ + ρ ^ (m + 2) * h ρ
        - vol1 * u x * (((m : ℝ) + 2) * ρ ^ (m + 1)) = 0 := by
      have key : ((m : ℝ) + 2) * ρ ^ (m + 1) * g ρ + ρ ^ (m + 2) * h ρ
          - vol1 * u x * (((m : ℝ) + 2) * ρ ^ (m + 1))
          = ρ ^ (m + 1) * (((m : ℝ) + 2) * g ρ + ρ * h ρ - ((m : ℝ) + 2) * vol1 * u x) := by
        rw [pow_succ]; ring
      rw [key]
      rcases eq_or_lt_of_le hρ.1 with h0 | h0
      · rw [← h0]; simp
      · have hode : ρ * h ρ + ((m : ℝ) + 2) * g ρ = ((m : ℝ) + 2) * vol1 * u x :=
          ball_ode x r u hu hΔ h0 hρ.2
        rw [show ((m : ℝ) + 2) * g ρ + ρ * h ρ - ((m : ℝ) + 2) * vol1 * u x = 0 by linarith,
          mul_zero]
    rwa [hval] at hd
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hD0
    (intervalIntegrable_const (c := (0 : ℝ)))
  simp only [intervalIntegral.integral_zero] at hFTC
  have hP0 : P 0 = 0 := by rw [hPdef]; simp
  have hQ0 : Q 0 = 0 := by rw [hQdef]; simp
  have hPQr : P r = Q r := by rw [hP0, hQ0] at hFTC; linarith
  have hvolball : (volume (Metric.ball x r)).toReal = r ^ (m + 2) * vol1 := by
    rw [Measure.addHaar_ball volume x hr.le, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity), finrank_euclideanSpace_fin]
  rw [ball_scaling x r hr u, hvolball,
    show (∫ z in Metric.ball (0 : ℝ^(m + 2)) 1, u (x + r • z)) = g r from rfl]
  have hPr : P r = r ^ (m + 2) * g r := rfl
  have hQr : Q r = vol1 * u x * r ^ (m + 2) := rfl
  rw [hPr, hQr] at hPQr
  rw [hPQr]; ring

/-- General (no harmonicity) divergence identity on the unit ball for `V(z)=u(x+ρz)•z`:
`ρ·(∫⟪∇u(x+ρz),z⟫) + (m+2)·(∫u(x+ρz)) = ∫_{∂B₁} u(x+ρz) dμHE`. -/
lemma ball_divergence_flux_identity (x : ℝ^(m + 2)) (ρ : ℝ) (u : (ℝ^(m + 2)) → ℝ)
    (hu : ContDiff ℝ 2 u) :
    ρ * (∫ z in Metric.ball (0 : ℝ^(m + 2)) 1, ⟪gradient u (x + ρ • z), z⟫)
      + ((m : ℝ) + 2) * (∫ z in Metric.ball (0 : ℝ^(m + 2)) 1, u (x + ρ • z))
      = ∫ z in Metric.sphere (0 : ℝ^(m + 2)) 1, u (x + ρ • z)
        ∂(μHE[m + 1] : Measure (ℝ^(m + 2))) := by
  have haff : Continuous (fun z : ℝ^(m + 2) => x + ρ • z) :=
    continuous_const.add (continuous_const.smul continuous_id)
  have hVcd : ContDiff ℝ 1 (fun z : ℝ^(m + 2) => u (x + ρ • z) • z) := by
    have h1 : ContDiff ℝ 1 (fun z : ℝ^(m + 2) => u (x + ρ • z)) :=
      (hu.of_le (by norm_num)).comp (by fun_prop)
    exact h1.smul contDiff_id
  have hdiv := divergence_theorem (isBoundedC1Domain_ball (0 : ℝ^(m + 2)) 1 one_pos)
    (isOutwardNormal_ball (0 : ℝ^(m + 2)) 1 one_pos) hVcd
  rw [frontier_ball (0 : ℝ^(m + 2)) one_ne_zero] at hdiv
  have hc1 : Continuous (fun z : ℝ^(m + 2) => (⟪gradient u (x + ρ • z), z⟫ : ℝ)) :=
    ((contDiff_gradient hu).continuous.comp haff).inner continuous_id
  have hc2 : Continuous (fun z : ℝ^(m + 2) => u (x + ρ • z)) := hu.continuous.comp haff
  have hint1 : IntegrableOn (fun z : ℝ^(m + 2) => (⟪gradient u (x + ρ • z), z⟫ : ℝ))
      (Metric.ball (0 : ℝ^(m + 2)) 1) :=
    (hc1.continuousOn.integrableOn_compact (isCompact_closedBall 0 1)).mono_set
      Metric.ball_subset_closedBall
  have hint2 : IntegrableOn (fun z : ℝ^(m + 2) => u (x + ρ • z))
      (Metric.ball (0 : ℝ^(m + 2)) 1) :=
    (hc2.continuousOn.integrableOn_compact (isCompact_closedBall 0 1)).mono_set
      Metric.ball_subset_closedBall
  rw [setIntegral_congr_fun measurableSet_ball (fun z _ => div_ball_field x ρ u hu z),
    integral_add (hint1.const_mul ρ) (hint2.const_mul _), integral_const_mul,
    integral_const_mul] at hdiv
  have hfluxeq : ∫ z in Metric.sphere (0 : ℝ^(m + 2)) 1,
        (⟪u (x + ρ • z) • z, (1 : ℝ)⁻¹ • (z - (0 : ℝ^(m + 2)))⟫ : ℝ)
        ∂(μHE[m + 1] : Measure (ℝ^(m + 2)))
      = ∫ z in Metric.sphere (0 : ℝ^(m + 2)) 1, u (x + ρ • z)
        ∂(μHE[m + 1] : Measure (ℝ^(m + 2))) := by
    refine setIntegral_congr_fun Metric.isClosed_sphere.measurableSet (fun z hz => ?_)
    rw [Metric.mem_sphere, dist_zero_right] at hz
    rw [inv_one, sub_zero, one_smul, real_inner_smul_left, real_inner_self_eq_norm_sq, hz]
    ring
  rw [hfluxeq] at hdiv
  exact hdiv

/-- The ball-Laplacian integral as a sphere flux: `∫_{B(x,s)} Δu = s^{m+1}·∫_{∂B₁} ⟪∇u(x+sω),ω⟫`. -/
lemma laplacian_ball_eq_sphere_flux (x : ℝ^(m + 2)) {s : ℝ} (hs : 0 < s) (u : (ℝ^(m + 2)) → ℝ)
    (hu : ContDiff ℝ 2 u) :
    ∫ y in Metric.ball x s, Laplacian.laplacian u y
      = s ^ (m + 1) • ∫ ω in Metric.sphere (0 : ℝ^(m + 2)) 1, ⟪gradient u (x + s • ω), ω⟫
          ∂(μHE[m + 1] : Measure (ℝ^(m + 2))) := by
  rw [integral_laplacian_ball x s hs u hu]
  have hrescale := setIntegral_sphere_rescale x hs
    (fun y => (⟪gradient u y, s⁻¹ • (y - x)⟫ : ℝ))
  have hsimp : ∀ ω : ℝ^(m + 2),
      (⟪gradient u (x + s • ω), s⁻¹ • ((x + s • ω) - x)⟫ : ℝ)
        = ⟪gradient u (x + s • ω), ω⟫ := by
    intro ω
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hs.ne', one_smul]
  simp only [hsimp] at hrescale
  exact hrescale

end

end AreaFormula


open MeasureTheory InnerProductSpace Set Laplacian Topology
open scoped ENNReal NNReal RealInnerProductSpace

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

/-- **Mean Value Property (ball version)** (Evans §2.2.2, Theorem 2). Stated for `n ≥ 2` (see
    `harmonic_sphereMeanValue`). Proved directly from the divergence theorem (no coarea formula):
    `∫_{B(x,r)} u = vol(B(x,r))·u(x)` via `AreaFormula.ball_integral_eq`, and the average divides
    out the volume. -/
theorem harmonic_ballMeanValue (hn : 2 ≤ n) (U : Set ℝⁿ) (u : ℝⁿ → ℝ)
    (hU : IsOpen U) (hu : IsHarmonic U u) (hu_c2 : ContDiff ℝ 2 u)
    (x : ℝⁿ) (r : ℝ) (hr : 0 < r)
    (hball : Metric.closedBall x r ⊆ U) :
    u x = ballMean u x r := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hΔ : ∀ y ∈ Metric.closedBall x r, Laplacian.laplacian u y = 0 :=
    fun y hy => hu y (hball hy)
  have hvol : (volume (Metric.ball x r)).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨(Metric.measure_ball_pos volume x hr).ne', measure_ball_lt_top.ne⟩
  rw [ballMean, setAverage_eq, measureReal_def,
    AreaFormula.ball_integral_eq x r hr u hu_c2 hΔ, smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ hvol, one_mul]

local notation "ℝ^" k => EuclideanSpace ℝ (Fin k)

open AreaFormula in
/-- `ballMean u x ρ = vol(B₁)⁻¹ · ∫_{B₁} u(x+ρz)` (the volume factor `ρ^{m+2}` cancels). -/
lemma ballMean_scaled (x : ℝ^(m + 2)) {ρ : ℝ} (hρ : 0 < ρ) (u : (ℝ^(m + 2)) → ℝ) :
    ballMean u x ρ = (volume (Metric.ball (0 : ℝ^(m + 2)) 1)).toReal⁻¹
      * ∫ z in Metric.ball (0 : ℝ^(m + 2)) 1, u (x + ρ • z) := by
  have hρne : ρ ≠ 0 := hρ.ne'
  have hv1 : (volume (Metric.ball (0 : ℝ^(m + 2)) 1)).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr
      ⟨(Metric.measure_ball_pos volume 0 one_pos).ne', measure_ball_lt_top.ne⟩
  rw [ballMean, setAverage_eq, measureReal_def, ball_scaling x ρ hρ u]
  have hvb : (volume (Metric.ball x ρ)).toReal
      = ρ ^ (m + 2) * (volume (Metric.ball (0 : ℝ^(m + 2)) 1)).toReal := by
    rw [Measure.addHaar_ball volume x hρ.le, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity), finrank_euclideanSpace_fin]
  rw [hvb, smul_eq_mul]
  field_simp

open AreaFormula in
/-- **Converse**: mean value property implies harmonic (Evans §2.2.2, Theorem 2, converse).
    Stated for `n ≥ 2`. Proved from the divergence theorem: the ball mean-value hypothesis makes
    `g(ρ) = ∫_{B₁} u(x₀+ρz)` constant, hence (via `ball_divergence_flux_identity`) the spherical
    integral is constant, so its derivative — the sphere flux, equal to `∫_{B(x₀,ρ)} Δu` — vanishes;
    continuity of `Δu` then forces `Δu(x₀) = 0`. -/
theorem meanValue_implies_harmonic (hn : 2 ≤ n) (U : Set ℝⁿ) (u : ℝⁿ → ℝ)
    (hU : IsOpen U) (hu_c2 : ContDiff ℝ 2 u)
    (hmv : ∀ x ∈ U, ∀ r > 0, Metric.closedBall x r ⊆ U → u x = ballMean u x r) :
    IsHarmonic U u := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  intro x₀ hx₀
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU x₀ hx₀
  set r₀ := ε / 2 with hr₀def
  have hr₀ : 0 < r₀ := by positivity
  have hball₀ : ∀ ρ, 0 < ρ → ρ ≤ r₀ → Metric.closedBall x₀ ρ ⊆ U := fun ρ _ hρr =>
    (Metric.closedBall_subset_ball (by rw [hr₀def] at hρr; linarith)).trans hεU
  set vol1 := (volume (Metric.ball (0 : ℝ^(m + 2)) 1)).toReal with hvol1
  have hv1 : vol1 ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr
      ⟨(Metric.measure_ball_pos volume 0 one_pos).ne', measure_ball_lt_top.ne⟩
  have hgconst : ∀ ρ ∈ Set.Ioo (0 : ℝ) r₀,
      (∫ z in Metric.ball (0 : ℝ^(m + 2)) 1, u (x₀ + ρ • z)) = vol1 * u x₀ := by
    intro ρ hρ
    have hmvρ := hmv x₀ hx₀ ρ hρ.1 (hball₀ ρ hρ.1 hρ.2.le)
    rw [ballMean_scaled x₀ hρ.1 u] at hmvρ
    rw [hmvρ, ← mul_assoc, mul_inv_cancel₀ hv1, one_mul]
  have hΨconst : ∀ ρ ∈ Set.Ioo (0 : ℝ) r₀,
      (∫ z in Metric.sphere (0 : ℝ^(m + 2)) 1, u (x₀ + ρ • z)
        ∂(μHE[m + 1] : Measure (ℝ^(m + 2)))) = ((m : ℝ) + 2) * (vol1 * u x₀) := by
    intro ρ hρ
    have hgderiv0 : (∫ z in Metric.ball (0 : ℝ^(m + 2)) 1, ⟪gradient u (x₀ + ρ • z), z⟫) = 0 := by
      have hEv : (fun ρ' => ∫ z in Metric.ball (0 : ℝ^(m + 2)) 1, u (x₀ + ρ' • z))
          =ᶠ[nhds ρ] (fun _ => vol1 * u x₀) :=
        Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hρ) (fun ρ' hρ' => hgconst ρ' hρ')
      have hd1 := hasDerivAt_ball_integral x₀ u hu_c2 ρ
      have hd2 : HasDerivAt (fun ρ' => ∫ z in Metric.ball (0 : ℝ^(m + 2)) 1, u (x₀ + ρ' • z)) 0 ρ :=
        (hasDerivAt_const ρ (vol1 * u x₀)).congr_of_eventuallyEq hEv
      exact hd1.unique hd2
    have hid := ball_divergence_flux_identity x₀ ρ u hu_c2
    rw [hgderiv0, hgconst ρ hρ, mul_zero, zero_add] at hid
    exact hid.symm
  have hlapzero : ∀ ρ ∈ Set.Ioo (0 : ℝ) r₀,
      ∫ y in Metric.ball x₀ ρ, Laplacian.laplacian u y = 0 := by
    intro ρ hρ
    have hΨderiv0 : (∫ ω in Metric.sphere (0 : ℝ^(m + 2)) 1, ⟪gradient u (x₀ + ρ • ω), ω⟫
        ∂(μHE[m + 1] : Measure (ℝ^(m + 2)))) = 0 := by
      have hEv : (fun ρ' => ∫ z in Metric.sphere (0 : ℝ^(m + 2)) 1, u (x₀ + ρ' • z)
            ∂(μHE[m + 1] : Measure (ℝ^(m + 2))))
          =ᶠ[nhds ρ] (fun _ => ((m : ℝ) + 2) * (vol1 * u x₀)) :=
        Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hρ) (fun ρ' hρ' => hΨconst ρ' hρ')
      have hd1 := hasDerivAt_sphere_integral x₀ u hu_c2 ρ
      have hd2 : HasDerivAt (fun ρ' => ∫ z in Metric.sphere (0 : ℝ^(m + 2)) 1, u (x₀ + ρ' • z)
          ∂(μHE[m + 1] : Measure (ℝ^(m + 2)))) 0 ρ :=
        (hasDerivAt_const ρ (((m : ℝ) + 2) * (vol1 * u x₀))).congr_of_eventuallyEq hEv
      exact hd1.unique hd2
    rw [laplacian_ball_eq_sphere_flux x₀ hρ.1 u hu_c2, hΨderiv0, smul_zero]
  by_contra hne
  have hc : 0 < |Laplacian.laplacian u x₀| := abs_pos.mpr hne
  obtain ⟨δ, hδ, hδb⟩ := Metric.continuousAt_iff.mp (continuous_laplacian hu_c2).continuousAt
    (|Laplacian.laplacian u x₀| / 2) (by positivity)
  have hmin : 0 < min δ r₀ := lt_min hδ hr₀
  set ρ := min δ r₀ / 2 with hρdef
  have hρ0 : 0 < ρ := by rw [hρdef]; linarith
  have hρr : ρ < r₀ := by rw [hρdef]; have := min_le_right δ r₀; linarith
  have hρδ : ρ < δ := by rw [hρdef]; have := min_le_left δ r₀; linarith
  have hlap0 := hlapzero ρ ⟨hρ0, hρr⟩
  have hvolρ : 0 < (volume (Metric.ball x₀ ρ)).toReal :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume x₀ hρ0).ne' measure_ball_lt_top.ne
  have hintΔ : IntegrableOn (Laplacian.laplacian u) (Metric.ball x₀ ρ) :=
    ((continuous_laplacian hu_c2).continuousOn.integrableOn_compact
      (isCompact_closedBall x₀ ρ)).mono_set Metric.ball_subset_closedBall
  have hintc : IntegrableOn (fun _ : ℝ^(m + 2) => Laplacian.laplacian u x₀) (Metric.ball x₀ ρ) :=
    (continuous_const.continuousOn.integrableOn_compact
      (isCompact_closedBall x₀ ρ)).mono_set Metric.ball_subset_closedBall
  have hsub : (∫ y in Metric.ball x₀ ρ,
        (Laplacian.laplacian u y - Laplacian.laplacian u x₀))
      = - ((volume (Metric.ball x₀ ρ)).toReal * Laplacian.laplacian u x₀) := by
    rw [integral_sub hintΔ hintc, hlap0, setIntegral_const, smul_eq_mul, measureReal_def]
    ring
  have hbd : ‖∫ y in Metric.ball x₀ ρ, (Laplacian.laplacian u y - Laplacian.laplacian u x₀)‖
      ≤ (|Laplacian.laplacian u x₀| / 2) * (volume (Metric.ball x₀ ρ)).toReal := by
    refine norm_setIntegral_le_of_norm_le_const measure_ball_lt_top (fun y hy => ?_)
    have hyδ : dist y x₀ < δ := lt_trans (Metric.mem_ball.mp hy) hρδ
    rw [Real.norm_eq_abs, ← Real.dist_eq]
    exact (hδb hyδ).le
  rw [hsub, norm_neg, Real.norm_eq_abs, abs_mul, abs_of_pos hvolρ] at hbd
  nlinarith [hbd, mul_pos hvolρ hc]

/-! ### Maximum Principle -/

/-- Rigidity: a continuous function `≤ M` on a ball whose mean equals `M` is `≡ M` on the ball.
    (`volume` is an open-positive measure, so a nonneg continuous function with zero integral over
    the open ball vanishes there.) -/
lemma const_on_ball_of_max (y : ℝⁿ) {s : ℝ} (hs : 0 < s) (u : ℝⁿ → ℝ)
    (hu : Continuous u) (M : ℝ)
    (hle : ∀ z ∈ Metric.ball y s, u z ≤ M) (hmean : ⨍ z in Metric.ball y s, u z = M) :
    ∀ z ∈ Metric.ball y s, u z = M := by
  have hvol : 0 < (volume (Metric.ball y s)).toReal :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume y hs).ne' measure_ball_lt_top.ne
  have hint : IntegrableOn u (Metric.ball y s) :=
    (hu.continuousOn.integrableOn_compact (isCompact_closedBall y s)).mono_set
      Metric.ball_subset_closedBall
  have hintc : IntegrableOn (fun _ : ℝⁿ => M) (Metric.ball y s) :=
    (continuous_const.continuousOn.integrableOn_compact (isCompact_closedBall y s)).mono_set
      Metric.ball_subset_closedBall
  have hintu_eq : (∫ z in Metric.ball y s, u z) = (volume (Metric.ball y s)).toReal * M := by
    have h := hmean
    rw [setAverage_eq, measureReal_def, smul_eq_mul] at h
    rw [inv_mul_eq_iff_eq_mul₀ hvol.ne'] at h
    exact h
  have hzero : (∫ z in Metric.ball y s, (M - u z)) = 0 := by
    rw [integral_sub hintc hint, setIntegral_const, smul_eq_mul, measureReal_def, hintu_eq]
    ring
  have hnn : 0 ≤ᵐ[volume.restrict (Metric.ball y s)] (fun z => M - u z) :=
    ae_restrict_of_forall_mem measurableSet_ball (fun z hz => sub_nonneg.mpr (hle z hz))
  have hintf : IntegrableOn (fun z => M - u z) (Metric.ball y s) := hintc.sub hint
  have hae : (fun z => M - u z) =ᵐ[volume.restrict (Metric.ball y s)] 0 :=
    (setIntegral_eq_zero_iff_of_nonneg_ae hnn hintf).mp hzero
  have heq : Set.EqOn (fun z => M - u z) 0 (Metric.ball y s) :=
    Measure.eqOn_of_ae_eq hae (continuous_const.sub hu).continuousOn continuousOn_const
      (by rw [Metric.isOpen_ball.interior_eq]; exact subset_closure)
  intro z hz
  have hz0 := heq hz
  simp only [Pi.zero_apply] at hz0
  linarith [hz0]

/-- **Strong Maximum Principle** (Evans §2.2.3, Theorem 4). Stated for `n ≥ 2` with `u ∈ C²` (the
    substantive setting; `IsHarmonic` on a merely continuous `u` is vacuous). A `C²` harmonic
    function on a connected open set attaining its maximum at an interior point is constant.
    Proof: the set `{u = max}` is relatively open in `U` (ball mean value + `const_on_ball_of_max`)
    and closed (continuity), hence all of `U` by connectedness. -/
theorem harmonic_strongMax (hn : 2 ≤ n) (U : Set ℝⁿ) (u : ℝⁿ → ℝ)
    (hU : IsOpen U) (hconn : IsConnected U)
    (hu : IsHarmonic U u) (hu_c2 : ContDiff ℝ 2 u)
    (x₀ : ℝⁿ) (hx₀ : x₀ ∈ U)
    (hmax : ∀ x ∈ U, u x ≤ u x₀) :
    ∀ x ∈ U, u x = u x₀ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  set M := u x₀ with hM
  have hopen : ∀ y ∈ U, u y = M → y ∈ interior {z | u z = M} := by
    intro y hyU hyM
    obtain ⟨ρ, hρ, hρU⟩ := Metric.isOpen_iff.mp hU y hyU
    set r₀ := ρ / 2 with hr₀
    have hr₀pos : 0 < r₀ := by positivity
    have hcball : Metric.closedBall y r₀ ⊆ U :=
      (Metric.closedBall_subset_ball (by rw [hr₀]; linarith)).trans hρU
    have hbmv := harmonic_ballMeanValue (by omega : 2 ≤ m + 2) U u hU hu hu_c2 y r₀ hr₀pos hcball
    have hmean : (⨍ z in Metric.ball y r₀, u z) = M := hbmv.symm.trans hyM
    have hle : ∀ z ∈ Metric.ball y r₀, u z ≤ M := fun z hz =>
      hmax z (hρU (Metric.ball_subset_ball (by rw [hr₀]; linarith) hz))
    have hconst := const_on_ball_of_max y hr₀pos u hu_c2.continuous M hle hmean
    exact mem_interior.mpr ⟨Metric.ball y r₀, fun z hz => hconst z hz, Metric.isOpen_ball,
      Metric.mem_ball_self hr₀pos⟩
  have hvopen : IsOpen {z : ℝ^(m + 2) | u z ≠ M} := isOpen_ne.preimage hu_c2.continuous
  have hdisj : Disjoint (interior {z | u z = M}) {z | u z ≠ M} := by
    rw [Set.disjoint_left]
    intro w hw1 hw2
    have hwM : w ∈ {z | u z = M} := interior_subset hw1
    exact hw2 hwM
  have hsub : U ⊆ interior {z | u z = M} ∪ {z | u z ≠ M} := by
    intro z hz
    by_cases hzm : u z = M
    · exact Or.inl (hopen z hz hzm)
    · exact Or.inr hzm
  have hcon : U ⊆ interior {z | u z = M} :=
    hconn.2.subset_left_of_subset_union isOpen_interior hvopen hdisj hsub
      ⟨x₀, hx₀, hopen x₀ hx₀ hM.symm⟩
  intro x hx
  have hxM : x ∈ {z | u z = M} := interior_subset (hcon hx)
  exact hxM

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

/-- **Green's second identity** on annular domain `B(x,r) \ B(x,ε)` (Riemannian `μHE[n−1]`).
    Evans §2.2.4 strategy:
    (1) Algebra:  v Δu − u Δv = div(v ∇u − u ∇v)      [product rule, cross terms cancel]
    (2) Gauss–Green on annulus: ∫_Ω div F = ∫_{S_r} F·ν dσ − ∫_{S_ε} F·ν dσ
        Sign: annulus outward normal on inner sphere is −ν (inward to B(x,ε)).
    Step (2) is now available via our `divergence_theorem` (`AreaFormula`): the annulus is
    `B(x,r) \ B̄(x,ε)`, handled by `setIntegral_diff` additivity of the two ball domains, with the
    inner sphere contributing the opposite sign. Uses `μHE[n−1]` (not raw `μH`) for correct
    constants. -/
lemma green_identity_annulus (hn : 2 ≤ n) (u v : ℝⁿ → ℝ)
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (x : ℝⁿ) (r ε : ℝ) (hr : 0 < r) (hε : 0 < ε) (hεr : ε < r) :
    ∫ y in Metric.ball x r \ Metric.ball x ε, (v y * Δ u y - u y * Δ v y)
    = (∫ y in Metric.sphere x r,
        (v y * ⟪gradient u y, ‖y - x‖⁻¹ • (y - x)⟫_ℝ -
         u y * ⟪gradient v y, ‖y - x‖⁻¹ • (y - x)⟫_ℝ)
        ∂(μHE[n - 1] : Measure ℝⁿ))
    - (∫ y in Metric.sphere x ε,
        (v y * ⟪gradient u y, ‖y - x‖⁻¹ • (y - x)⟫_ℝ -
         u y * ⟪gradient v y, ‖y - x‖⁻¹ • (y - x)⟫_ℝ)
        ∂(μHE[n - 1] : Measure ℝⁿ)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  simp only [show m + 2 - 1 = m + 1 from rfl]
  have key : ∀ s : ℝ,
      (∫ y in Metric.sphere x s,
          (v y * ⟪gradient u y, ‖y - x‖⁻¹ • (y - x)⟫_ℝ -
           u y * ⟪gradient v y, ‖y - x‖⁻¹ • (y - x)⟫_ℝ)
          ∂(μHE[m + 1] : Measure (ℝ^(m + 2))))
      = -(∫ y in Metric.sphere x s,
          (u y * ⟪gradient v y, s⁻¹ • (y - x)⟫_ℝ -
           v y * ⟪gradient u y, s⁻¹ • (y - x)⟫_ℝ)
          ∂(μHE[m + 1] : Measure (ℝ^(m + 2)))) := by
    intro s
    rw [← integral_neg]
    refine setIntegral_congr_fun Metric.isClosed_sphere.measurableSet (fun y hy => ?_)
    rw [Metric.mem_sphere, dist_eq_norm] at hy
    rw [hy]; ring
  rw [key r, key ε]
  have hLHS : (∫ y in Metric.ball x r \ Metric.ball x ε, (v y * Δ u y - u y * Δ v y))
      = -(∫ y in Metric.ball x r \ Metric.ball x ε, (u y * Δ v y - v y * Δ u y)) := by
    rw [← integral_neg]
    refine setIntegral_congr_fun (measurableSet_ball.diff measurableSet_ball) (fun y _ => ?_)
    ring
  rw [hLHS]
  have hA := AreaFormula.green_identity_annulus x r ε hr hε hεr u v hu hv
  linarith [hA]

/-- Flux integrand for a radial power `c·‖·‖^p`: `⟪∇(c‖·‖^p), ‖y‖⁻¹y⟫ = c·p·‖y‖^{p-1}`. -/
lemma flux_rpow (c p : ℝ) (y : ℝⁿ) (hy : y ≠ 0) :
    ⟪gradient (fun x : ℝⁿ => c * ‖x‖ ^ p) y, ‖y‖⁻¹ • y⟫_ℝ = c * p * ‖y‖ ^ (p - 1) := by
  have hpos : (0 : ℝ) < ‖y‖ := norm_pos_iff.mpr hy
  have hfd : HasFDerivAt (fun x : ℝⁿ => c * ‖x‖ ^ p)
      (c • ((p * ‖y‖ ^ (p - 2)) • realInnerL y)) y :=
    (hasFDerivAt_norm_rpow_of_ne y hy p).const_mul c
  rw [inner_gradient_left hfd.differentiableAt, hfd.fderiv]
  simp only [ContinuousLinearMap.smul_apply, realInnerL_apply, real_inner_smul_right, smul_eq_mul,
    real_inner_self_eq_norm_sq]
  have hAB : ‖y‖ ^ (p - 2) * ((‖y‖ : ℝ)⁻¹ * ‖y‖ ^ 2) = ‖y‖ ^ (p - 1) := by
    rw [show (‖y‖ : ℝ)⁻¹ = ‖y‖ ^ (-1 : ℝ) from (Real.rpow_neg_one _).symm,
      show (‖y‖ : ℝ) ^ 2 = ‖y‖ ^ (2 : ℝ) from (Real.rpow_two _).symm,
      ← Real.rpow_add hpos, ← Real.rpow_add hpos]
    congr 1; ring
  linear_combination c * p * hAB

/-- Flux integrand for `c·log‖·‖`: `⟪∇(c·log‖·‖), ‖y‖⁻¹y⟫ = c·‖y‖⁻¹`. -/
lemma flux_log (c : ℝ) (y : ℝⁿ) (hy : y ≠ 0) :
    ⟪gradient (fun x : ℝⁿ => c * Real.log ‖x‖) y, ‖y‖⁻¹ • y⟫_ℝ = c * ‖y‖⁻¹ := by
  have hne : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  have hnorm : HasFDerivAt (fun x : ℝⁿ => ‖x‖) (‖y‖⁻¹ • realInnerL y) y := by
    have h := hasFDerivAt_norm_rpow_of_ne y hy 1
    simp only [Real.rpow_one, one_mul, show (1 : ℝ) - 2 = -1 by norm_num, Real.rpow_neg_one] at h
    exact h
  have hlog : HasFDerivAt (fun x : ℝⁿ => Real.log ‖x‖)
      ((‖y‖)⁻¹ • (‖y‖⁻¹ • realInnerL y)) y :=
    (Real.hasDerivAt_log hne).comp_hasFDerivAt y hnorm
  have hfd : HasFDerivAt (fun x : ℝⁿ => c * Real.log ‖x‖)
      (c • ((‖y‖)⁻¹ • (‖y‖⁻¹ • realInnerL y))) y := hlog.const_mul c
  rw [inner_gradient_left hfd.differentiableAt, hfd.fderiv]
  simp only [ContinuousLinearMap.smul_apply, realInnerL_apply, real_inner_smul_right, smul_eq_mul,
    real_inner_self_eq_norm_mul_norm]
  field_simp

open AreaFormula in
/-- Total outward normal flux of `∇Φ` through `∂B(0, ε)` equals `−1` (dimension `n = m+2 ≥ 2`).

    Uses the Riemannian surface measure `μHE[n−1]` (the one our Gauss–Green machinery produces):
    the flux integrand is the constant radial derivative `Φ'(ε)`, and `Φ` is normalized against the
    true surface area `σ(∂B) = n·ωₙ·ε^{n−1}` (`= μHE`), giving exactly `−1`. (With the *raw*
    Hausdorff `μH[n−1]` this would be `−1/c₀ ≠ −1` for `n ≥ 3`.) -/
lemma totalFlux_aux (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∫ y in Metric.sphere (0 : ℝ^(m + 2)) ε, ⟪gradient fundamentalSolution y, ‖y‖⁻¹ • y⟫_ℝ
      ∂(μHE[m + 1] : Measure (ℝ^(m + 2))) = -1 := by
  set ω := (volume (Metric.ball (0 : ℝ^(m + 2)) 1)).toReal with hω
  have hωpos : 0 < ω :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne
  have hσ : (μHE[m + 1] (Metric.sphere (0 : ℝ^(m + 2)) ε)).toReal
      = ((m : ℝ) + 2) * (volume (Metric.ball (0 : ℝ^(m + 2)) ε)).toReal / ε :=
    sphere_surfaceMeasure 0 ε hε
  have hvolε : (volume (Metric.ball (0 : ℝ^(m + 2)) ε)).toReal = ε ^ (m + 2) * ω := by
    rw [Measure.addHaar_ball volume 0 hε.le, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity), finrank_euclideanSpace_fin]
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    have hΦeq : (fundamentalSolution : (ℝ^2) → ℝ) = fun x => -(1 / (2 * Real.pi)) * Real.log ‖x‖ :=
      funext (fun x => by simp [fundamentalSolution])
    have hK : ∀ y ∈ Metric.sphere (0 : ℝ^2) ε,
        ⟪gradient fundamentalSolution y, ‖y‖⁻¹ • y⟫_ℝ = -(1 / (2 * Real.pi)) * ε⁻¹ := by
      intro y hy
      rw [Metric.mem_sphere, dist_zero_right] at hy
      have hyne : y ≠ 0 := by intro h; rw [h, norm_zero] at hy; exact hε.ne' hy.symm
      rw [hΦeq, flux_log _ _ hyne, hy]
    have hω2 : ω = Real.pi := by
      rw [hω, EuclideanSpace.volume_ball]
      simp only [ENNReal.ofReal_one, one_pow, one_mul, Fintype.card_fin, Nat.zero_add,
        Nat.cast_ofNat]
      rw [ENNReal.toReal_ofReal (by positivity), Real.sq_sqrt Real.pi_pos.le,
        show ((2 : ℝ) / 2 + 1) = 2 by norm_num, Real.Gamma_two, div_one]
    rw [setIntegral_congr_fun Metric.isClosed_sphere.measurableSet hK, setIntegral_const,
      smul_eq_mul, measureReal_def, hσ, hvolε, hω2]
    have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
    ring
  · set c := (1 / (((m + 2 : ℕ) : ℝ) * (((m + 2 : ℕ) : ℝ) - 2) * ω)) with hc
    have hΦeq : (fundamentalSolution : (ℝ^(m + 2)) → ℝ)
        = fun x => c * ‖x‖ ^ (2 - ((m + 2 : ℕ) : ℝ)) := by
      funext x
      simp only [fundamentalSolution, show (m + 2 : ℕ) ≠ 0 from by omega,
        show (m + 2 : ℕ) ≠ 1 from by omega, show (m + 2 : ℕ) ≠ 2 from by omega, if_false]
      rw [hc, hω]
    have hK : ∀ y ∈ Metric.sphere (0 : ℝ^(m + 2)) ε,
        ⟪gradient fundamentalSolution y, ‖y‖⁻¹ • y⟫_ℝ
        = c * (2 - ((m + 2 : ℕ) : ℝ)) * ε ^ ((2 - ((m + 2 : ℕ) : ℝ)) - 1) := by
      intro y hy
      rw [Metric.mem_sphere, dist_zero_right] at hy
      have hyne : y ≠ 0 := by intro h; rw [h, norm_zero] at hy; exact hε.ne' hy.symm
      rw [hΦeq, flux_rpow _ _ _ hyne, hy]
    rw [setIntegral_congr_fun Metric.isClosed_sphere.measurableSet hK, setIntegral_const,
      smul_eq_mul, measureReal_def, hσ, hvolε]
    have hεcombine : ε ^ (m + 2) / ε * ε ^ ((2 - ((m + 2 : ℕ) : ℝ)) - 1) = 1 := by
      rw [show ε ^ (m + 2) = ε ^ ((m + 2 : ℕ) : ℝ) from (Real.rpow_natCast ε (m + 2)).symm,
        div_eq_mul_inv, show (ε : ℝ)⁻¹ = ε ^ (-1 : ℝ) from (Real.rpow_neg_one ε).symm,
        ← Real.rpow_add hε, ← Real.rpow_add hε]
      rw [show ((m + 2 : ℕ) : ℝ) + -1 + ((2 - ((m + 2 : ℕ) : ℝ)) - 1) = 0 by push_cast; ring,
        Real.rpow_zero]
    have hconst : ((m : ℝ) + 2) * ω * (c * (2 - ((m + 2 : ℕ) : ℝ))) = -1 := by
      have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hmpos.ne'
      have h1 : ((m + 2 : ℕ) : ℝ) ≠ 0 := by push_cast; positivity
      have h2 : ((m + 2 : ℕ) : ℝ) - 2 ≠ 0 := by push_cast; simpa using hmR
      rw [hc]
      field_simp
      push_cast
      ring
    calc ((m : ℝ) + 2) * (ε ^ (m + 2) * ω) / ε
            * (c * (2 - ((m + 2 : ℕ) : ℝ)) * ε ^ ((2 - ((m + 2 : ℕ) : ℝ)) - 1))
        = (((m : ℝ) + 2) * ω * (c * (2 - ((m + 2 : ℕ) : ℝ))))
            * (ε ^ (m + 2) / ε * ε ^ ((2 - ((m + 2 : ℕ) : ℝ)) - 1)) := by ring
      _ = -1 := by rw [hconst, hεcombine]; ring

/-- Total outward normal flux of `∇Φ` through `∂B(0, ε)` equals `−1` (`n ≥ 2`, Riemannian `μHE`). -/
lemma fundamentalSolution_totalFlux (hn : 2 ≤ n) (ε : ℝ) (hε : 0 < ε) :
    ∫ y in Metric.sphere (0 : ℝⁿ) ε,
      ⟪gradient fundamentalSolution y, ‖y‖⁻¹ • y⟫_ℝ
      ∂(μHE[n - 1] : Measure ℝⁿ) = -1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  exact totalFlux_aux m ε hε

section GreenBoundaryHelpers
open AreaFormula
variable {m : ℕ}

/-- Shifted total flux: `∫_{∂B(x,ε)} ⟪∇Φ(y−x), ν⟫ dμHE = −1`, via μHE translation-invariance. -/
lemma totalFlux_shifted (x : ℝ^(m + 2)) (ε : ℝ) (hε : 0 < ε) :
    ∫ y in Metric.sphere x ε,
      ⟪gradient fundamentalSolution (y - x), ‖y - x‖⁻¹ • (y - x)⟫_ℝ
      ∂(μHE[m + 1] : Measure (ℝ^(m + 2))) = -1 := by
  have hmp : MeasurePreserving (fun z : ℝ^(m + 2) => x + z)
      (μHE[m + 1] : Measure (ℝ^(m + 2))) (μHE[m + 1] : Measure (ℝ^(m + 2))) :=
    ⟨measurable_const_add x, map_add_μHE x⟩
  have hpre : (fun z : ℝ^(m + 2) => x + z) ⁻¹' (Metric.sphere x ε) = Metric.sphere 0 ε := by
    ext z; simp [dist_eq_norm]
  rw [← hmp.setIntegral_preimage_emb (measurableEmbedding_addLeft x)
      (fun y => ⟪gradient fundamentalSolution (y - x), ‖y - x‖⁻¹ • (y - x)⟫_ℝ)
      (Metric.sphere x ε), hpre]
  simp only [add_sub_cancel_left]
  exact totalFlux_aux m ε hε

/-- The μHE sphere average of a continuous function tends to its value at the centre as `ε → 0`. -/
lemma sphere_average_tendsto (x : ℝ^(m + 2)) (f : (ℝ^(m + 2)) → ℝ) (hf : Continuous f) :
    Filter.Tendsto (fun ε => ⨍ y in Metric.sphere x ε, f y ∂(μHE[m + 1] : Measure (ℝ^(m + 2))))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (f x)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro δ hδ
  obtain ⟨ρ, hρ, hρf⟩ := Metric.continuous_iff.mp hf x (δ / 2) (by positivity)
  refine ⟨ρ, hρ, fun ε hε hερ => ?_⟩
  have hε0 : 0 < ε := hε
  rw [Real.dist_eq, sub_zero, abs_of_pos hε0] at hερ
  have hσfin : (μHE[m + 1] (Metric.sphere x ε)) ≠ ∞ := by
    have h := surfaceMeasure_frontier_lt_top (isBoundedC1Domain_ball x ε hε0)
    rw [frontier_ball x hε0.ne'] at h; exact h.ne
  have hσtoReal : 0 < (μHE[m + 1] (Metric.sphere x ε)).toReal := by
    rw [sphere_surfaceMeasure x ε hε0]
    have : 0 < (volume (Metric.ball x ε)).toReal :=
      ENNReal.toReal_pos (Metric.measure_ball_pos volume x hε0).ne' measure_ball_lt_top.ne
    positivity
  have hσne : (μHE[m + 1] (Metric.sphere x ε)) ≠ 0 := fun h => by
    rw [h, ENNReal.toReal_zero] at hσtoReal; exact lt_irrefl 0 hσtoReal
  haveI hfinm : IsFiniteMeasure ((μHE[m + 1] : Measure (ℝ^(m + 2))).restrict
      (Metric.sphere x ε)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.mpr hσfin⟩
  obtain ⟨M, hM⟩ := (isCompact_sphere x ε).exists_bound_of_continuousOn hf.continuousOn
  have hintf : IntegrableOn f (Metric.sphere x ε) (μHE[m + 1]) :=
    (integrable_const M).mono' hf.aestronglyMeasurable
      (ae_restrict_of_forall_mem Metric.isClosed_sphere.measurableSet (fun y hy => hM y hy))
  have hintc : IntegrableOn (fun _ : ℝ^(m + 2) => f x) (Metric.sphere x ε) (μHE[m + 1]) :=
    integrable_const (f x)
  have hbnd : ∀ y ∈ Metric.sphere x ε, ‖f y - f x‖ ≤ δ / 2 := by
    intro y hy
    rw [Metric.mem_sphere] at hy
    rw [Real.norm_eq_abs, ← Real.dist_eq]
    exact (hρf y (by rw [hy]; exact hερ)).le
  have hkey : (⨍ y in Metric.sphere x ε, f y ∂μHE[m + 1]) - f x
      = ⨍ y in Metric.sphere x ε, (f y - f x) ∂μHE[m + 1] := by
    have h1 : (⨍ y in Metric.sphere x ε, (f y - f x) ∂μHE[m + 1])
        = (⨍ y in Metric.sphere x ε, f y ∂μHE[m + 1])
          - ⨍ _y in Metric.sphere x ε, f x ∂μHE[m + 1] := by
      rw [setAverage_eq, setAverage_eq, setAverage_eq, ← smul_sub, ← integral_sub hintf hintc]
    rw [h1, setAverage_const hσne hσfin]
  rw [Real.dist_eq, hkey, setAverage_eq, measureReal_def, smul_eq_mul, abs_mul,
    abs_of_pos (inv_pos.mpr hσtoReal)]
  have hI : |∫ y in Metric.sphere x ε, (f y - f x) ∂μHE[m + 1]|
      ≤ δ / 2 * (μHE[m + 1] (Metric.sphere x ε)).toReal := by
    rw [← Real.norm_eq_abs]
    exact norm_setIntegral_le_of_norm_le_const (lt_top_iff_ne_top.mpr hσfin) hbnd
  calc (μHE[m + 1] (Metric.sphere x ε)).toReal⁻¹
        * |∫ y in Metric.sphere x ε, (f y - f x) ∂μHE[m + 1]|
      ≤ (μHE[m + 1] (Metric.sphere x ε)).toReal⁻¹
          * (δ / 2 * (μHE[m + 1] (Metric.sphere x ε)).toReal) := by
        apply mul_le_mul_of_nonneg_left hI (le_of_lt (inv_pos.mpr hσtoReal))
    _ = δ / 2 := by field_simp
    _ < δ := by linarith

/-- The fundamental solution is radial: it depends only on `‖z‖`. -/
lemma Phi_radial (z z' : ℝ^(m + 2)) (hnorm : ‖z‖ = ‖z'‖) :
    fundamentalSolution z = fundamentalSolution z' := by
  simp only [fundamentalSolution, hnorm]

/-- The flux integrand `⟪∇Φ z, ‖z‖⁻¹z⟫` depends only on `‖z‖`. -/
lemma flux_radial (z z' : ℝ^(m + 2)) (hz : z ≠ 0) (hz' : z' ≠ 0) (hnorm : ‖z‖ = ‖z'‖) :
    ⟪gradient fundamentalSolution z, ‖z‖⁻¹ • z⟫_ℝ
      = ⟪gradient fundamentalSolution z', ‖z'‖⁻¹ • z'⟫_ℝ := by
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    have hΦeq : (fundamentalSolution : (ℝ^2) → ℝ) = fun w => -(1 / (2 * Real.pi)) * Real.log ‖w‖ :=
      funext (fun w => by simp [fundamentalSolution])
    rw [hΦeq, flux_log _ _ hz, flux_log _ _ hz', hnorm]
  · set c := (1 / (((m + 2 : ℕ) : ℝ) * (((m + 2 : ℕ) : ℝ) - 2) *
      (volume (Metric.ball (0 : ℝ^(m + 2)) 1)).toReal)) with hc
    have hΦeq : (fundamentalSolution : (ℝ^(m + 2)) → ℝ)
        = fun w => c * ‖w‖ ^ (2 - ((m + 2 : ℕ) : ℝ)) := by
      funext w
      simp only [fundamentalSolution, show (m + 2 : ℕ) ≠ 0 from by omega,
        show (m + 2 : ℕ) ≠ 1 from by omega, show (m + 2 : ℕ) ≠ 2 from by omega, if_false]
      rw [hc]
    rw [hΦeq, flux_rpow _ _ _ hz, flux_rpow _ _ _ hz', hnorm]

/-- Integrability of a continuous function on a sphere against `μHE` (finite measure there). -/
lemma integrableOn_sphere_of_continuousOn {g : (ℝ^(m + 2)) → ℝ} (x : ℝ^(m + 2)) {ε : ℝ}
    (hε : 0 < ε) (hg : ContinuousOn g (Metric.sphere x ε)) :
    IntegrableOn g (Metric.sphere x ε) (μHE[m + 1]) := by
  have hσfin : (μHE[m + 1] (Metric.sphere x ε)) ≠ ∞ := by
    have h := surfaceMeasure_frontier_lt_top (isBoundedC1Domain_ball x ε hε)
    rw [frontier_ball x hε.ne'] at h; exact h.ne
  haveI : IsFiniteMeasure ((μHE[m + 1] : Measure (ℝ^(m + 2))).restrict (Metric.sphere x ε)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.mpr hσfin⟩
  obtain ⟨M, hM⟩ := (isCompact_sphere x ε).exists_bound_of_continuousOn hg
  exact (integrable_const M).mono' (hg.aestronglyMeasurable Metric.isClosed_sphere.measurableSet)
    (ae_restrict_of_forall_mem Metric.isClosed_sphere.measurableSet (fun y hy => hM y hy))

/-- The boundary-integral limit, given Term A → 0. -/
lemma green_boundary_test (x : ℝ^(m + 2)) (f : (ℝ^(m + 2)) → ℝ) (hf : ContDiff ℝ 2 f)
    (e₀ : ℝ^(m + 2)) (he₀ : ‖e₀‖ = 1)
    (hA : Filter.Tendsto
      (fun ε => fundamentalSolution (ε • e₀) * ∫ y in Metric.ball x ε, Laplacian.laplacian f y)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) :
    Filter.Tendsto
      (fun ε => ∫ y in Metric.sphere x ε,
        (fundamentalSolution (y - x) * ⟪gradient f y, ‖y - x‖⁻¹ • (y - x)⟫_ℝ
         - f y * ⟪gradient fundamentalSolution (y - x), ‖y - x‖⁻¹ • (y - x)⟫_ℝ)
        ∂(μHE[m + 1] : Measure (ℝ^(m + 2))))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (f x)) := by
  have hgradf : Continuous (gradient f) := (contDiff_gradient hf).continuous
  have hkey : ∀ ε : ℝ, 0 < ε →
      (∫ y in Metric.sphere x ε,
        (fundamentalSolution (y - x) * ⟪gradient f y, ‖y - x‖⁻¹ • (y - x)⟫_ℝ
         - f y * ⟪gradient fundamentalSolution (y - x), ‖y - x‖⁻¹ • (y - x)⟫_ℝ)
        ∂(μHE[m + 1] : Measure (ℝ^(m + 2))))
      = (fundamentalSolution (ε • e₀) * ∫ y in Metric.ball x ε, Laplacian.laplacian f y)
        + ⨍ y in Metric.sphere x ε, f y ∂(μHE[m + 1] : Measure (ℝ^(m + 2))) := by
    intro ε hε
    set y₀ : ℝ^(m + 2) := x + ε • e₀ with hy₀
    have hy₀sub : y₀ - x = ε • e₀ := by rw [hy₀]; abel
    have hy₀subnorm : ‖y₀ - x‖ = ε := by
      rw [hy₀sub, norm_smul, he₀, mul_one, Real.norm_eq_abs, abs_of_pos hε]
    have hy₀subne : y₀ - x ≠ 0 := by rw [← norm_ne_zero_iff, hy₀subnorm]; exact hε.ne'
    have hymem : ∀ y ∈ Metric.sphere x ε, ‖y - x‖ = ε := fun y hy => by
      rw [Metric.mem_sphere, dist_eq_norm] at hy; exact hy
    have hyne : ∀ y ∈ Metric.sphere x ε, y - x ≠ 0 := fun y hy => by
      rw [← norm_ne_zero_iff, hymem y hy]; exact hε.ne'
    set K := ⟪gradient fundamentalSolution (y₀ - x), ‖y₀ - x‖⁻¹ • (y₀ - x)⟫_ℝ with hKdef
    have hBconst : ∀ y ∈ Metric.sphere x ε,
        ⟪gradient fundamentalSolution (y - x), ‖y - x‖⁻¹ • (y - x)⟫_ℝ = K :=
      fun y hy => flux_radial (y - x) (y₀ - x) (hyne y hy) hy₀subne (by rw [hymem y hy, hy₀subnorm])
    have hΦconst : ∀ y ∈ Metric.sphere x ε,
        fundamentalSolution (y - x) = fundamentalSolution (ε • e₀) :=
      fun y hy => Phi_radial (y - x) (ε • e₀)
        (by rw [hymem y hy, norm_smul, he₀, mul_one, Real.norm_eq_abs, abs_of_pos hε])
    rw [setIntegral_congr_fun Metric.isClosed_sphere.measurableSet
      (fun y hy => by rw [hΦconst y hy, hBconst y hy])]
    have hνcont : ContinuousOn (fun y => (‖y - x‖⁻¹ • (y - x) : ℝ^(m + 2))) (Metric.sphere x ε) :=
      ContinuousOn.smul
        ((continuous_norm.comp (continuous_id.sub continuous_const)).continuousOn.inv₀
          (fun y hy => by show ‖y - x‖ ≠ 0; rw [hymem y hy]; exact hε.ne'))
        (continuous_id.sub continuous_const).continuousOn
    have hint1 : IntegrableOn (fun y => fundamentalSolution (ε • e₀)
        * ⟪gradient f y, ‖y - x‖⁻¹ • (y - x)⟫_ℝ) (Metric.sphere x ε) (μHE[m + 1]) :=
      integrableOn_sphere_of_continuousOn x hε
        (continuousOn_const.mul (hgradf.continuousOn.inner hνcont))
    have hint2 : IntegrableOn (fun y => f y * K) (Metric.sphere x ε) (μHE[m + 1]) :=
      integrableOn_sphere_of_continuousOn x hε (hf.continuous.continuousOn.mul continuousOn_const)
    rw [integral_sub hint1 hint2]
    have hAeq : (∫ y in Metric.sphere x ε,
          fundamentalSolution (ε • e₀) * ⟪gradient f y, ‖y - x‖⁻¹ • (y - x)⟫_ℝ ∂μHE[m + 1])
        = fundamentalSolution (ε • e₀) * ∫ y in Metric.ball x ε, Laplacian.laplacian f y := by
      rw [integral_const_mul]
      congr 1
      rw [integral_laplacian_ball x ε hε f hf]
      exact setIntegral_congr_fun Metric.isClosed_sphere.measurableSet
        (fun y hy => by rw [hymem y hy])
    have hσfin : (μHE[m + 1] (Metric.sphere x ε)) ≠ ∞ := by
      have h := surfaceMeasure_frontier_lt_top (isBoundedC1Domain_ball x ε hε)
      rw [frontier_ball x hε.ne'] at h; exact h.ne
    have hσtoReal : 0 < (μHE[m + 1] (Metric.sphere x ε)).toReal := by
      rw [sphere_surfaceMeasure x ε hε]
      have : 0 < (volume (Metric.ball x ε)).toReal :=
        ENNReal.toReal_pos (Metric.measure_ball_pos volume x hε).ne' measure_ball_lt_top.ne
      positivity
    have hKσ : K * (μHE[m + 1] (Metric.sphere x ε)).toReal = -1 := by
      have ht := totalFlux_shifted x ε hε
      rw [setIntegral_congr_fun Metric.isClosed_sphere.measurableSet hBconst, setIntegral_const,
        smul_eq_mul, measureReal_def] at ht
      linarith [ht]
    have hBeq : (∫ y in Metric.sphere x ε, f y * K ∂μHE[m + 1])
        = -⨍ y in Metric.sphere x ε, f y ∂μHE[m + 1] := by
      rw [integral_mul_const, setAverage_eq, measureReal_def, smul_eq_mul]
      have hσne : (μHE[m + 1] (Metric.sphere x ε)).toReal ≠ 0 := hσtoReal.ne'
      field_simp
      linear_combination (∫ y in Metric.sphere x ε, f y ∂μHE[m + 1]) * hKσ
    rw [hAeq, hBeq]; ring
  have hEv : (fun ε => ∫ y in Metric.sphere x ε,
        (fundamentalSolution (y - x) * ⟪gradient f y, ‖y - x‖⁻¹ • (y - x)⟫_ℝ
         - f y * ⟪gradient fundamentalSolution (y - x), ‖y - x‖⁻¹ • (y - x)⟫_ℝ)
        ∂(μHE[m + 1] : Measure (ℝ^(m + 2))))
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun ε => (fundamentalSolution (ε • e₀) * ∫ y in Metric.ball x ε, Laplacian.laplacian f y)
        + ⨍ y in Metric.sphere x ε, f y ∂(μHE[m + 1] : Measure (ℝ^(m + 2)))) :=
    Filter.eventuallyEq_of_mem self_mem_nhdsWithin (fun ε hε => hkey ε hε)
  rw [Filter.tendsto_congr' hEv]
  simpa using hA.add (sphere_average_tendsto x f hf.continuous)

/-- `ε² · |log ε| → 0` as `ε → 0⁺` (via `|log ε| ≤ ε⁻¹` on `(0,1]`). -/
lemma sq_mul_abs_log_tendsto :
    Filter.Tendsto (fun ε : ℝ => ε ^ 2 * |Real.log ε|) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  apply squeeze_zero_norm' (a := fun ε : ℝ => ε)
  · filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds (show (0:ℝ) < 1 by norm_num))] with ε hε0 hε1
    have hε0' : 0 < ε := hε0
    have hε1' : ε ≤ 1 := hε1
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hlog : |Real.log ε| ≤ ε⁻¹ := by
      rw [abs_of_nonpos (Real.log_nonpos hε0'.le hε1'), ← Real.log_inv]
      calc Real.log ε⁻¹ ≤ ε⁻¹ - 1 := Real.log_le_sub_one_of_pos (by positivity)
        _ ≤ ε⁻¹ := by linarith
    calc ε ^ 2 * |Real.log ε| ≤ ε ^ 2 * ε⁻¹ :=
          mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = ε := by field_simp
  · exact (continuous_id.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds

/-- Term A tends to `0`: `Φ(ε•e₀) · ∫_{B(x,ε)} Δf → 0` as `ε → 0⁺`. -/
lemma termA_tendsto (x : ℝ^(m + 2)) (f : (ℝ^(m + 2)) → ℝ) (hf : ContDiff ℝ 2 f)
    (e₀ : ℝ^(m + 2)) (he₀ : ‖e₀‖ = 1) :
    Filter.Tendsto
      (fun ε => fundamentalSolution (ε • e₀) * ∫ y in Metric.ball x ε, Laplacian.laplacian f y)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  set ω := (volume (Metric.ball (0 : ℝ^(m + 2)) 1)).toReal with hω
  obtain ⟨M, hM⟩ := (isCompact_closedBall x 1).exists_bound_of_continuousOn
    (continuous_laplacian hf).continuousOn
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM x (Metric.mem_closedBall_self zero_le_one))
  have hrate : Filter.Tendsto
      (fun ε => |fundamentalSolution (ε • e₀)| * (volume (Metric.ball x ε)).toReal)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hnorm : ∀ ε : ℝ, 0 < ε → ‖ε • e₀‖ = ε := fun ε hε => by
      rw [norm_smul, he₀, mul_one, Real.norm_eq_abs, abs_of_pos hε]
    have hvol : ∀ ε : ℝ, 0 < ε → (volume (Metric.ball x ε)).toReal = ε ^ (m + 2) * ω :=
      fun ε hε => by
        rw [Measure.addHaar_ball volume x hε.le, ENNReal.toReal_mul,
          ENNReal.toReal_ofReal (by positivity), finrank_euclideanSpace_fin]
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0
      have hcongr : (fun ε => |fundamentalSolution (ε • e₀)| * (volume (Metric.ball x ε)).toReal)
          =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
          (fun ε => (1 / (2 * Real.pi)) * ω * (ε ^ 2 * |Real.log ε|)) := by
        filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
        rw [show (fundamentalSolution (ε • e₀) : ℝ) = -(1 / (2 * Real.pi)) * Real.log ε from by
          rw [show (fundamentalSolution (ε • e₀) : ℝ)
            = -(1 / (2 * Real.pi)) * Real.log ‖ε • e₀‖ from by simp [fundamentalSolution],
            hnorm ε hε], hvol ε hε, abs_mul, abs_neg,
          abs_of_pos (by positivity : (0:ℝ) < 1 / (2 * Real.pi))]
        ring
      rw [Filter.tendsto_congr' hcongr]
      simpa using (sq_mul_abs_log_tendsto.const_mul ((1 / (2 * Real.pi)) * ω))
    · have hcongr : (fun ε => |fundamentalSolution (ε • e₀)| * (volume (Metric.ball x ε)).toReal)
          =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
          (fun ε => |1 / (((m + 2 : ℕ) : ℝ) * (((m + 2 : ℕ) : ℝ) - 2) * ω)| * ω * ε ^ 2) := by
        filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
        have hΦ : (fundamentalSolution (ε • e₀) : ℝ)
            = (1 / (((m + 2 : ℕ) : ℝ) * (((m + 2 : ℕ) : ℝ) - 2) * ω))
              * ε ^ (2 - ((m + 2 : ℕ) : ℝ)) := by
          rw [show (fundamentalSolution (ε • e₀) : ℝ)
            = (1 / (((m + 2 : ℕ) : ℝ) * (((m + 2 : ℕ) : ℝ) - 2) * ω))
              * ‖ε • e₀‖ ^ (2 - ((m + 2 : ℕ) : ℝ)) from by
            simp only [fundamentalSolution, show (m + 2 : ℕ) ≠ 0 from by omega,
              show (m + 2 : ℕ) ≠ 1 from by omega, show (m + 2 : ℕ) ≠ 2 from by omega, if_false]
            rw [hω], hnorm ε hε]
        rw [hΦ, hvol ε hε, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hε _)]
        have hexp : ε ^ (2 - ((m + 2 : ℕ) : ℝ)) * ε ^ (m + 2) = ε ^ 2 := by
          rw [show ε ^ (m + 2) = ε ^ ((m + 2 : ℕ) : ℝ) from (Real.rpow_natCast ε (m + 2)).symm,
            ← Real.rpow_add hε,
            show (2 : ℝ) - ((m + 2 : ℕ) : ℝ) + ((m + 2 : ℕ) : ℝ) = ((2 : ℕ) : ℝ) by push_cast; ring,
            Real.rpow_natCast]
        linear_combination (|1 / (((m + 2 : ℕ) : ℝ) * (((m + 2 : ℕ) : ℝ) - 2) * ω)| * ω) * hexp
      rw [Filter.tendsto_congr' hcongr]
      have h2 : Filter.Tendsto (fun ε : ℝ => ε ^ 2) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        have : Filter.Tendsto (fun ε : ℝ => ε ^ 2) (nhds 0) (nhds 0) := by
          have := (continuous_pow 2).tendsto (0 : ℝ); simpa using this
        exact this.mono_left nhdsWithin_le_nhds
      simpa using h2.const_mul (|1 / (((m + 2 : ℕ) : ℝ) * (((m + 2 : ℕ) : ℝ) - 2) * ω)| * ω)
  apply squeeze_zero_norm'
    (a := fun ε => M * (|fundamentalSolution (ε • e₀)| * (volume (Metric.ball x ε)).toReal))
  · filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds (show (0:ℝ) < 1 by norm_num))] with ε hε0 hε1
    have hε1' : ε ≤ 1 := hε1
    rw [norm_mul, Real.norm_eq_abs]
    have hball : Metric.ball x ε ⊆ Metric.closedBall x 1 :=
      Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall hε1')
    have hint : ‖∫ y in Metric.ball x ε, Laplacian.laplacian f y‖
        ≤ M * (volume (Metric.ball x ε)).toReal :=
      norm_setIntegral_le_of_norm_le_const measure_ball_lt_top (fun y hy => hM y (hball hy))
    calc |fundamentalSolution (ε • e₀)| * ‖∫ y in Metric.ball x ε, Laplacian.laplacian f y‖
        ≤ |fundamentalSolution (ε • e₀)| * (M * (volume (Metric.ball x ε)).toReal) :=
          mul_le_mul_of_nonneg_left hint (abs_nonneg _)
      _ = M * (|fundamentalSolution (ε • e₀)| * (volume (Metric.ball x ε)).toReal) := by ring
  · simpa using hrate.const_mul M

end GreenBoundaryHelpers

/-- Boundary integral from Green's identity converges to `f(x)` as ε → 0 (Riemannian `μHE[n−1]`). -/
lemma green_boundary_tendsto_f (hn : 2 ≤ n) (f : ℝⁿ → ℝ) (hf : ContDiff ℝ 2 f)
    (hf_supp : HasCompactSupport f) (x : ℝⁿ) :
    Filter.Tendsto
      (fun ε => ∫ y in Metric.sphere x ε,
        (fundamentalSolution (y - x) * ⟪gradient f y, ‖y - x‖⁻¹ • (y - x)⟫_ℝ
         - f y * ⟪gradient fundamentalSolution (y - x), ‖y - x‖⁻¹ • (y - x)⟫_ℝ)
        ∂(μHE[n - 1] : Measure ℝⁿ))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (f x)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have he₀ : ‖(EuclideanSpace.single (0 : Fin (m + 2)) (1 : ℝ))‖ = 1 := by
    simp [EuclideanSpace.norm_single]
  exact green_boundary_test x f hf _ he₀ (termA_tendsto x f hf _ he₀)

/-- The fundamental solution is measurable (built from `‖·‖`, `log`, `rpow`). -/
lemma fundamentalSolution_aestronglyMeasurable :
    AEStronglyMeasurable (fundamentalSolution : ℝⁿ → ℝ) volume := by
  unfold fundamentalSolution
  split_ifs <;>
    first
      | exact aestronglyMeasurable_const
      | (apply Measurable.aestronglyMeasurable; fun_prop)

/-- The fundamental solution is locally integrable. -/
lemma fundamentalSolution_locallyIntegrable :
    LocallyIntegrable (fundamentalSolution : ℝⁿ → ℝ) volume := by
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · refine ⟨Metric.ball 0 1, Metric.ball_mem_nhds 0 one_pos, ?_⟩
    exact (integrable_norm_iff fundamentalSolution_aestronglyMeasurable.restrict).mp
      fundamentalSolution_norm_integrableOn_unitBall
  · refine ⟨Metric.closedBall x (‖x‖ / 2), Metric.closedBall_mem_nhds x (by positivity), ?_⟩
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hsub : Metric.closedBall x (‖x‖ / 2) ⊆ ({0} : Set ℝⁿ)ᶜ := by
      intro z hz
      rw [Metric.mem_closedBall] at hz
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      rintro rfl
      rw [dist_zero_left] at hz
      linarith
    exact (fundamentalSolution_contDiff_off_zero.continuousOn.mono hsub).integrableOn_compact
      (isCompact_closedBall x (‖x‖ / 2))

/-- Reflection–translation `y ↦ x − y` preserves compact support. -/
lemma hasCompactSupport_comp_sub {F : Type*} [NormedAddCommGroup F] {g : ℝⁿ → F}
    (hgc : HasCompactSupport g) (x : ℝⁿ) : HasCompactSupport (fun y => g (x - y)) := by
  have : (fun y => g (x - y)) = g ∘ (fun y => x - y) := rfl
  rw [this]
  exact hgc.comp_homeomorph (Homeomorph.subLeft x)

/-- **Derivative of a `Φ`-convolution lands on the smooth compact-support factor.**
    For `Φ` locally integrable and `g` a `C¹` function with compact support, the map
    `z ↦ ∫ Φ(y)·g(z−y) dy` is differentiable with derivative `∫ Φ(y)·(Dg)(z−y) dy`. -/
lemma pot_hasFDerivAt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Φ : ℝⁿ → ℝ) (hΦ : LocallyIntegrable Φ)
    (g : ℝⁿ → F) (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) (x : ℝⁿ) :
    HasFDerivAt (fun z => ∫ y, Φ y • g (z - y))
      (∫ y, Φ y • fderiv ℝ g (x - y)) x := by
  have hgdiff : Differentiable ℝ g := hg.differentiable one_ne_zero
  -- `z' ↦ g(z'−y)` differentiates to `Dg(z−y)`.
  have hfd : ∀ (y z : ℝⁿ), HasFDerivAt (fun z' => g (z' - y)) (fderiv ℝ g (z - y)) z := by
    intro y z
    have hsub : HasFDerivAt (fun z' : ℝⁿ => z' - y) (ContinuousLinearMap.id ℝ ℝⁿ) z :=
      (hasFDerivAt_id z).sub_const y
    simpa using (hgdiff (z - y)).hasFDerivAt.comp z hsub
  -- bounds for the derivative of `g`
  set S := tsupport (fderiv ℝ g) with hS
  have hScompact : IsCompact S := hgc.fderiv ℝ
  obtain ⟨M₀, hM₀⟩ := hScompact.exists_bound_of_continuousOn
    (hg.continuous_fderiv one_ne_zero).continuousOn
  set M := max M₀ 0 with hMdef
  have hM0 : 0 ≤ M := le_max_right _ _
  have hM : ∀ y, ‖fderiv ℝ g y‖ ≤ M := by
    intro y
    by_cases hy : y ∈ S
    · exact le_trans (hM₀ y hy) (le_max_left _ _)
    · have hy' : y ∉ tsupport (fderiv ℝ g) := by rw [hS] at hy; exact hy
      rw [image_eq_zero_of_notMem_tsupport hy', norm_zero]; exact hM0
  set K := (fun p : ℝⁿ × ℝⁿ => p.1 - p.2) '' (Metric.closedBall x 1 ×ˢ S) with hK
  have hKcompact : IsCompact K :=
    ((isCompact_closedBall x 1).prod hScompact).image (continuous_fst.sub continuous_snd)
  -- the dominating function
  set bound : ℝⁿ → ℝ := K.indicator (fun y => M * ‖Φ y‖) with hbound
  have hbound_int : Integrable bound := by
    rw [hbound, integrable_indicator_iff hKcompact.measurableSet]
    exact ((hΦ.integrableOn_isCompact hKcompact).norm.const_mul M)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume)
    (F := fun z y => Φ y • g (z - y))
    (F' := fun z y => Φ y • fderiv ℝ g (z - y))
    (bound := bound) (Metric.ball_mem_nhds x one_pos)
    (Filter.Eventually.of_forall fun z => ?_) ?_ ?_ ?_ hbound_int ?_
  · -- F z measurable in y
    exact hΦ.aestronglyMeasurable.smul
      ((hg.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
  · -- F x integrable
    exact hΦ.integrable_smul_right_of_hasCompactSupport
      (hg.continuous.comp (continuous_const.sub continuous_id))
      (hasCompactSupport_comp_sub hgc x)
  · -- F' x measurable
    refine hΦ.aestronglyMeasurable.smul ?_
    exact ((hg.continuous_fderiv one_ne_zero).comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable
  · -- bound
    refine Filter.Eventually.of_forall fun y z hz => ?_
    rw [Metric.mem_ball, dist_eq_norm] at hz
    rw [norm_smul, Real.norm_eq_abs, ← Real.norm_eq_abs]
    by_cases hyK : y ∈ K
    · rw [hbound, Set.indicator_of_mem hyK]
      rw [mul_comm M (‖Φ y‖)]
      exact mul_le_mul_of_nonneg_left (hM (z - y)) (norm_nonneg _)
    · have hzero : fderiv ℝ g (z - y) = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hmem
        exact hyK ⟨(z, z - y),
          ⟨Metric.mem_closedBall.mpr (by rw [dist_eq_norm]; linarith [hz.le]), hmem⟩,
          by show z - (z - y) = y; abel⟩
      rw [hzero, norm_zero, mul_zero, hbound, Set.indicator_of_notMem hyK]
  · -- differentiability
    exact Filter.Eventually.of_forall fun y z _ => (hfd y z).const_smul (Φ y)

/-- Change of variables: `∫ Φ(x−y)·f(y) = ∫ Φ(y)·f(x−y)`. -/
lemma newtonianPotential_eq (f : ℝⁿ → ℝ) (x : ℝⁿ) :
    newtonianPotential f x = ∫ y, fundamentalSolution y * f (x - y) := by
  calc newtonianPotential f x
      = ∫ y, (fun w => fundamentalSolution w * f (x - w)) (x - y) := by
        simp only [newtonianPotential, sub_sub_cancel]
    _ = ∫ y, fundamentalSolution y * f (x - y) :=
        MeasureTheory.integral_sub_left_eq_self
          (fun w => fundamentalSolution w * f (x - w)) volume x

/-- Integrability of `y ↦ Φ(y) • G(z−y)` for `Φ` loc. integrable, `G` continuous, compact support. -/
lemma pot_integrable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Φ : ℝⁿ → ℝ) (hΦ : LocallyIntegrable Φ) (G : ℝⁿ → F) (hG : Continuous G)
    (hGc : HasCompactSupport G) (z : ℝⁿ) : Integrable (fun y => Φ y • G (z - y)) :=
  hΦ.integrable_smul_right_of_hasCompactSupport (hG.comp (continuous_const.sub continuous_id))
    (hasCompactSupport_comp_sub hGc z)

/-- Local copy of `Δ(f(·−y))(x) = (Δf)(x−y)` (Heat.lean's `laplacian_comp_sub`, not imported here). -/
lemma laplacian_comp_sub' (f : ℝⁿ → ℝ) (y x : ℝⁿ) :
    Laplacian.laplacian (fun z => f (z - y)) x = Laplacian.laplacian f (x - y) := by
  rw [congr_fun (laplacian_eq_iteratedFDeriv_stdOrthonormalBasis (fun z => f (z - y))) x,
      congr_fun (laplacian_eq_iteratedFDeriv_stdOrthonormalBasis f) (x - y)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [iteratedFDeriv_comp_sub (𝕜 := ℝ) 2 y x]

/-- Change of variables `∫ Φ(x−y)·g(y) = ∫ Φ(y)·g(x−y)`. -/
lemma conv_comm (Φ : ℝⁿ → ℝ) (g : ℝⁿ → ℝ) (x : ℝⁿ) :
    (∫ y, Φ (x - y) * g y) = ∫ y, Φ y * g (x - y) := by
  calc (∫ y, Φ (x - y) * g y)
      = ∫ y, (fun w => Φ w * g (x - w)) (x - y) := by simp only [sub_sub_cancel]
    _ = ∫ y, Φ y * g (x - y) :=
        MeasureTheory.integral_sub_left_eq_self (fun w => Φ w * g (x - w)) volume x

/-- **Part A of the representation formula**: `Δ(Newtonian potential of f) = ∫ Φ(x−y)·Δf(y) dy`.
    The Laplacian is moved onto the smooth compact-support factor `f` via `pot_hasFDerivAt`
    (scalar differentiation-under-the-integral, avoiding the `precompR`/CLM convolution route). -/
lemma laplacian_newtonianPotential (f : ℝⁿ → ℝ) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (x : ℝⁿ) :
    Laplacian.laplacian (newtonianPotential f) x
      = ∫ y, fundamentalSolution (x - y) * Laplacian.laplacian f y := by
  set Φ := (fundamentalSolution : ℝⁿ → ℝ) with hΦdef
  have hΦ : LocallyIntegrable Φ := fundamentalSolution_locallyIntegrable
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hfdc : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  have hfdcs : HasCompactSupport (fderiv ℝ f) := hfc.fderiv ℝ
  have hf1' : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  -- the potential as a Φ-convolution (change of variables, uniform in the base point)
  have hpot : (fun z => ∫ y, Φ y • f (z - y)) = newtonianPotential f := by
    funext z; simp only [smul_eq_mul]; exact (newtonianPotential_eq f z).symm
  have hspace : ∀ z, HasFDerivAt (fun z => ∫ y, Φ y • f (z - y))
      (∫ y, Φ y • fderiv ℝ f (z - y)) z := fun z => pot_hasFDerivAt Φ hΦ f hf1 hfc z
  have hgrad_int : ∀ z, Integrable (fun y => Φ y • fderiv ℝ f (z - y)) :=
    fun z => pot_integrable Φ hΦ (fderiv ℝ f) hfdc hfdcs z
  have hdF : DifferentiableAt ℝ (fderiv ℝ (fun z => ∫ y, Φ y • f (z - y))) x := by
    have hfe : fderiv ℝ (fun z => ∫ y, Φ y • f (z - y))
        = fun z => ∫ y, Φ y • fderiv ℝ f (z - y) := funext (fun z => (hspace z).fderiv)
    rw [hfe]
    exact (pot_hasFDerivAt Φ hΦ (fderiv ℝ f) hf1' hfdcs x).differentiableAt
  -- second directional derivative passes under the integral, for each basis direction
  have hper : ∀ i, iteratedFDeriv ℝ 2 (fun z => ∫ y, Φ y • f (z - y)) x
        ![stdOrthonormalBasis ℝ ℝⁿ i, stdOrthonormalBasis ℝ ℝⁿ i]
      = ∫ y, iteratedFDeriv ℝ 2 (fun z => Φ y • f (z - y)) x
          ![stdOrthonormalBasis ℝ ℝⁿ i, stdOrthonormalBasis ℝ ℝⁿ i] := by
    intro i
    set v := stdOrthonormalBasis ℝ ℝⁿ i with hv
    have hh1 : ContDiff ℝ 1 (fun w => fderiv ℝ f w v) :=
      (ContinuousLinearMap.apply ℝ ℝ v).contDiff.comp hf1'
    have hhc : HasCompactSupport (fun w => fderiv ℝ f w v) :=
      hfdcs.comp_left (g := fun L : ℝⁿ →L[ℝ] ℝ => L v) (by simp)
    have hdir_int : Integrable (fun y => Φ y • fderiv ℝ (fun w => fderiv ℝ f w v) (x - y)) :=
      pot_integrable Φ hΦ (fderiv ℝ (fun w => fderiv ℝ f w v))
        (hh1.continuous_fderiv one_ne_zero) (hhc.fderiv ℝ) x
    rw [iteratedFDeriv_two_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    rw [← fderiv_fderiv_apply (fun z => ∫ y, Φ y • f (z - y)) x v v hdF]
    have hfun : (fun z => fderiv ℝ (fun z => ∫ y, Φ y • f (z - y)) z v)
        = fun z => ∫ y, Φ y • (fun w => fderiv ℝ f w v) (z - y) := by
      funext z
      rw [(hspace z).fderiv, ContinuousLinearMap.integral_apply (hgrad_int z)]
      simp only [ContinuousLinearMap.smul_apply]
    rw [hfun, (pot_hasFDerivAt Φ hΦ (fun w => fderiv ℝ f w v) hh1 hhc x).fderiv,
      ContinuousLinearMap.integral_apply hdir_int]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show (Φ y • fderiv ℝ (fun w => fderiv ℝ f w v) (x - y)) v
        = iteratedFDeriv ℝ 2 (fun z => Φ y • f (z - y)) x ![v, v]
    have hcda : ContDiffAt ℝ 2 (fun z => f (z - y)) x :=
      (hf.comp (contDiff_id.sub contDiff_const)).contDiffAt
    have hdfd : DifferentiableAt ℝ (fderiv ℝ f) (x - y) :=
      (hf1'.differentiable one_ne_zero).differentiableAt
    rw [ContinuousLinearMap.smul_apply,
      show iteratedFDeriv ℝ 2 (fun z => Φ y • f (z - y)) x ![v, v]
          = Φ y • iteratedFDeriv ℝ 2 (fun z => f (z - y)) x ![v, v] from by
        rw [show (fun z => Φ y • f (z - y)) = (Φ y) • (fun z => f (z - y)) from rfl,
          iteratedFDeriv_const_smul_apply hcda, ContinuousMultilinearMap.smul_apply]]
    congr 1
    rw [iteratedFDeriv_comp_sub (𝕜 := ℝ) 2 y x, iteratedFDeriv_two_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    rw [fderiv_fderiv_apply f (x - y) v v hdfd]
  -- integrability of each diagonal-second-derivative integrand
  have hint : ∀ i, Integrable (fun y => iteratedFDeriv ℝ 2 (fun z => Φ y • f (z - y)) x
      ![stdOrthonormalBasis ℝ ℝⁿ i, stdOrthonormalBasis ℝ ℝⁿ i]) := by
    intro i
    set v := stdOrthonormalBasis ℝ ℝⁿ i with hv
    have hg2c : Continuous (fun w => iteratedFDeriv ℝ 2 f w ![v, v]) :=
      (ContinuousMultilinearMap.apply ℝ (fun _ => ℝⁿ) ℝ ![v, v]).continuous.comp
        (hf.continuous_iteratedFDeriv (by norm_num))
    have hg2cs : HasCompactSupport (fun w => iteratedFDeriv ℝ 2 f w ![v, v]) :=
      (hfc.iteratedFDeriv (𝕜 := ℝ) 2).comp_left
        (g := fun L : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => ℝⁿ) ℝ => L ![v, v]) (by simp)
    have hrw : (fun y => iteratedFDeriv ℝ 2 (fun z => Φ y • f (z - y)) x ![v, v])
        = fun y => Φ y • (fun w => iteratedFDeriv ℝ 2 f w ![v, v]) (x - y) := by
      funext y
      have hcda : ContDiffAt ℝ 2 (fun z => f (z - y)) x :=
        (hf.comp (contDiff_id.sub contDiff_const)).contDiffAt
      rw [show (fun z => Φ y • f (z - y)) = (Φ y) • (fun z => f (z - y)) from rfl,
        iteratedFDeriv_const_smul_apply hcda, ContinuousMultilinearMap.smul_apply,
        iteratedFDeriv_comp_sub (𝕜 := ℝ) 2 y x]
    rw [hrw]
    exact pot_integrable Φ hΦ (fun w => iteratedFDeriv ℝ 2 f w ![v, v]) hg2c hg2cs x
  -- assemble
  rw [← hpot, laplacian_integral_eq (fun z y => Φ y • f (z - y)) x hper hint]
  have hlap : ∀ y, Laplacian.laplacian (fun z => Φ y • f (z - y)) x
      = Φ y • Laplacian.laplacian f (x - y) := by
    intro y
    have hcda : ContDiffAt ℝ 2 (fun z => f (z - y)) x :=
      (hf.comp (contDiff_id.sub contDiff_const)).contDiffAt
    rw [show (fun z => Φ y • f (z - y)) = (Φ y) • (fun z => f (z - y)) from rfl,
      laplacian_smul (Φ y) hcda, laplacian_comp_sub']
  rw [integral_congr_ae (Filter.Eventually.of_forall hlap)]
  simp only [smul_eq_mul]
  exact (conv_comm Φ (Laplacian.laplacian f) x).symm

/-- **Cutoff of the fundamental solution.** For `ε > 0` there is a globally `C²` function `w`
    that agrees with `Φ(·−x)` on the neighborhood `{y : ε/2 < ‖y−x‖}` of the closed annulus,
    obtained by multiplying `Φ(·−x)` by a smooth cutoff that vanishes near `x`. -/
lemma mollified_fund (x : ℝⁿ) (ε : ℝ) (hε : 0 < ε) :
    ∃ w : ℝⁿ → ℝ, ContDiff ℝ 2 w
      ∧ ∀ y, ε / 2 < ‖y - x‖ → w =ᶠ[nhds y] fun z => fundamentalSolution (z - x) := by
  set b : ContDiffBump x := ⟨ε / 4, ε / 2, by positivity, by linarith⟩ with hb
  refine ⟨fun y => (1 - b y) * fundamentalSolution (y - x), ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : dist y x < ε / 4
    · have hzero : (fun z => (1 - b z) * fundamentalSolution (z - x)) =ᶠ[nhds y] fun _ => 0 := by
        refine Filter.eventuallyEq_of_mem
          (IsOpen.mem_nhds Metric.isOpen_ball (Metric.mem_ball.mpr hy)) (fun z hz => ?_)
        rw [Metric.mem_ball] at hz
        have : b z = 1 := b.one_of_mem_closedBall (Metric.mem_closedBall.mpr hz.le)
        rw [this]; ring
      exact contDiffAt_const.congr_of_eventuallyEq hzero
    · have hle : ε / 4 ≤ dist y x := not_lt.mp hy
      have hyne : y - x ≠ 0 := by
        rw [sub_ne_zero]; intro h; rw [h, dist_self] at hle; linarith
      have hb_cd : ContDiffAt ℝ 2 (fun z => 1 - b z) y :=
        contDiffAt_const.sub (b.contDiff.contDiffAt)
      have hΦ_cd : ContDiffAt ℝ 2 (fun z => fundamentalSolution (z - x)) y := by
        have h1 : ContDiffAt ℝ 2 (fundamentalSolution (n := n)) (y - x) :=
          (fundamentalSolution_contDiff_off_zero.contDiffAt
            (isOpen_compl_singleton.mem_nhds (Set.mem_compl_singleton_iff.mpr hyne))).of_le le_top
        have hsub : ContDiffAt ℝ 2 (fun z : ℝⁿ => z - x) y :=
          contDiffAt_id.sub contDiffAt_const
        exact ContDiffAt.comp (g := (fundamentalSolution : ℝⁿ → ℝ))
          (f := fun z : ℝⁿ => z - x) y h1 hsub
      exact hb_cd.mul hΦ_cd
  · intro y hy
    refine Filter.eventuallyEq_of_mem
      (IsOpen.mem_nhds (isOpen_lt continuous_const (continuous_norm.comp
        (continuous_id.sub continuous_const))) hy) (fun z hz => ?_)
    simp only [Set.mem_setOf_eq] at hz
    have : b z = 0 := b.zero_of_le_dist (by rw [dist_eq_norm]; exact hz.le)
    rw [this]; ring

/-- Gradient respects local equality. -/
lemma gradient_congr {f g : ℝⁿ → ℝ} {y : ℝⁿ} (h : f =ᶠ[nhds y] g) :
    gradient f y = gradient g y := by
  unfold gradient
  rw [h.fderiv_eq]

/-- Translation of the gradient: `∇(g(·−x))(y) = (∇g)(y−x)`. -/
lemma gradient_comp_sub (g : ℝⁿ → ℝ) (x y : ℝⁿ) (hg : DifferentiableAt ℝ g (y - x)) :
    gradient (fun z => g (z - x)) y = gradient g (y - x) := by
  unfold gradient
  congr 1
  have h := hg.hasFDerivAt.comp y ((hasFDerivAt_id y).sub_const x)
  simpa using h.fderiv

/-- **Green's identity on the annulus for the fundamental solution** (the singular case).
    Applying `green_identity_annulus` to the cutoff `w` (which agrees with `Φ(·−x)` on the
    annulus) gives, since `Φ` is harmonic there and `f` vanishes on the outer sphere:
    `∫_{annulus} Φ(x−y)·Δf = − ∮_{∂B(x,ε)} (Φ⟪∇f,ν⟫ − f⟪∇Φ,ν⟫)`. -/
lemma green_annulus_fund (hn : 2 ≤ n) (x : ℝⁿ) (f : ℝⁿ → ℝ) (hf : ContDiff ℝ 2 f)
    (r ε : ℝ) (hε : 0 < ε) (hεr : ε < r)
    (hsupp : ∀ y, r ≤ ‖y - x‖ → f y = 0)
    (hsuppg : ∀ y, r ≤ ‖y - x‖ → gradient f y = 0) :
    ∫ y in Metric.ball x r \ Metric.ball x ε, fundamentalSolution (x - y) * Δ f y
    = - ∫ y in Metric.sphere x ε,
        (fundamentalSolution (y - x) * ⟪gradient f y, ‖y - x‖⁻¹ • (y - x)⟫_ℝ
         - f y * ⟪gradient fundamentalSolution (y - x), ‖y - x‖⁻¹ • (y - x)⟫_ℝ)
        ∂(μHE[n - 1] : Measure ℝⁿ) := by
  obtain ⟨w, hw_cd, hw_agree⟩ := mollified_fund x ε hε
  have hval : ∀ y, ε / 2 < ‖y - x‖ → w y = fundamentalSolution (y - x) :=
    fun y hy => (hw_agree y hy).eq_of_nhds
  have hΦdiff : ∀ y, ε / 2 < ‖y - x‖ →
      DifferentiableAt ℝ (fundamentalSolution : ℝⁿ → ℝ) (y - x) := fun y hy => by
    have hne : y - x ≠ 0 := by rw [← norm_pos_iff]; linarith
    have hcd : ContDiffAt ℝ 2 (fundamentalSolution : ℝⁿ → ℝ) (y - x) :=
      (fundamentalSolution_contDiff_off_zero.contDiffAt
        (isOpen_compl_singleton.mem_nhds (Set.mem_compl_singleton_iff.mpr hne))).of_le le_top
    exact hcd.differentiableAt (by norm_num)
  have hgrad : ∀ y, ε / 2 < ‖y - x‖ →
      gradient w y = gradient (fundamentalSolution : ℝⁿ → ℝ) (y - x) := fun y hy => by
    rw [gradient_congr (hw_agree y hy), gradient_comp_sub fundamentalSolution x y (hΦdiff y hy)]
  have hlap : ∀ y, ε / 2 < ‖y - x‖ → Δ w y = 0 := fun y hy => by
    have hne : y - x ≠ 0 := by rw [← norm_pos_iff]; linarith
    rw [(laplacian_congr_nhds (hw_agree y hy)).eq_of_nhds, laplacian_comp_sub',
      fundamentalSolution_harmonic_off_zero (y - x) hne]
  have hann : ∀ y ∈ Metric.ball x r \ Metric.ball x ε, ε / 2 < ‖y - x‖ := by
    intro y hy
    simp only [Set.mem_diff, Metric.mem_ball, not_lt, dist_eq_norm] at hy
    linarith [hy.2]
  have hgia := green_identity_annulus hn w f hw_cd hf x r ε (lt_trans hε hεr) hε hεr
  have e1 : (∫ y in Metric.ball x r \ Metric.ball x ε, (f y * Δ w y - w y * Δ f y))
      = -∫ y in Metric.ball x r \ Metric.ball x ε, fundamentalSolution (x - y) * Δ f y := by
    rw [← integral_neg]
    refine setIntegral_congr_fun (measurableSet_ball.diff measurableSet_ball) (fun y hy => ?_)
    have hy2 := hann y hy
    have hsym : fundamentalSolution (y - x) = fundamentalSolution (x - y) := by
      have hnn : ‖y - x‖ = ‖x - y‖ := norm_sub_rev y x
      simp only [fundamentalSolution, hnn]
    rw [hlap y hy2, hval y hy2, hsym]; ring
  have e2 : (∫ y in Metric.sphere x r,
        (f y * ⟪gradient w y, ‖y - x‖⁻¹ • (y - x)⟫_ℝ
         - w y * ⟪gradient f y, ‖y - x‖⁻¹ • (y - x)⟫_ℝ)
        ∂(μHE[n - 1] : Measure ℝⁿ)) = 0 := by
    have hz : ∀ y ∈ Metric.sphere x r,
        (f y * ⟪gradient w y, ‖y - x‖⁻¹ • (y - x)⟫_ℝ
         - w y * ⟪gradient f y, ‖y - x‖⁻¹ • (y - x)⟫_ℝ) = 0 := by
      intro y hy
      rw [Metric.mem_sphere, dist_eq_norm] at hy
      rw [hsupp y (le_of_eq hy.symm), hsuppg y (le_of_eq hy.symm)]; simp
    rw [setIntegral_congr_fun Metric.isClosed_sphere.measurableSet hz, integral_zero]
  have e3 : (∫ y in Metric.sphere x ε,
        (f y * ⟪gradient w y, ‖y - x‖⁻¹ • (y - x)⟫_ℝ
         - w y * ⟪gradient f y, ‖y - x‖⁻¹ • (y - x)⟫_ℝ)
        ∂(μHE[n - 1] : Measure ℝⁿ))
      = -∫ y in Metric.sphere x ε,
        (fundamentalSolution (y - x) * ⟪gradient f y, ‖y - x‖⁻¹ • (y - x)⟫_ℝ
         - f y * ⟪gradient fundamentalSolution (y - x), ‖y - x‖⁻¹ • (y - x)⟫_ℝ)
        ∂(μHE[n - 1] : Measure ℝⁿ) := by
    rw [← integral_neg]
    refine setIntegral_congr_fun Metric.isClosed_sphere.measurableSet (fun y hy => ?_)
    rw [Metric.mem_sphere, dist_eq_norm] at hy
    have hy2 : ε / 2 < ‖y - x‖ := by rw [hy]; linarith
    rw [hgrad y hy2, hval y hy2]; ring
  rw [e1, e2, e3] at hgia
  linarith [hgia]

/-- **Part B of the representation formula**: `∫ Φ(x−y)·Δf(y) dy = −f(x)`.  The `ε→0` limit of
    the annulus identity: the near part `∫_{B(x,ε)}` vanishes and the boundary term tends to
    `f(x)` (`green_boundary_tendsto_f`). -/
lemma fund_poisson_integral (hn : 2 ≤ n) (f : ℝⁿ → ℝ) (hf : ContDiff ℝ 2 f)
    (hf_supp : HasCompactSupport f) (x : ℝⁿ) :
    (∫ y, fundamentalSolution (x - y) * Δ f y) = - f x := by
  have hΦloc : LocallyIntegrable (fundamentalSolution : ℝⁿ → ℝ) := fundamentalSolution_locallyIntegrable
  have hΔc : Continuous (Δ f) := by
    rw [show Δ f = fun z => ∑ i, iteratedFDeriv ℝ 2 f z
        ![stdOrthonormalBasis ℝ ℝⁿ i, stdOrthonormalBasis ℝ ℝⁿ i] from
      funext (fun z => congr_fun (laplacian_eq_iteratedFDeriv_stdOrthonormalBasis f) z)]
    refine continuous_finset_sum _ (fun i _ => ?_)
    exact (ContinuousMultilinearMap.apply ℝ (fun _ => ℝⁿ) ℝ
        ![stdOrthonormalBasis ℝ ℝⁿ i, stdOrthonormalBasis ℝ ℝⁿ i]).continuous.comp
      (hf.continuous_iteratedFDeriv (by norm_num))
  have hΔcs : HasCompactSupport (Δ f) := by
    apply IsCompact.of_isClosed_subset hf_supp (isClosed_tsupport _)
    apply closure_minimal _ (isClosed_tsupport _)
    intro y hy
    by_contra hyn
    have hf0 : f =ᶠ[nhds y] 0 :=
      Filter.eventuallyEq_of_mem (isOpen_compl_iff.mpr (isClosed_tsupport f) |>.mem_nhds hyn)
        (fun z hz => image_eq_zero_of_notMem_tsupport hz)
    exact hy (by rw [(laplacian_congr_nhds hf0).eq_of_nhds]; exact congr_fun laplacian_const y)
  have hg : Integrable (fun y => fundamentalSolution (x - y) * Δ f y) := by
    have hpot := pot_integrable (fundamentalSolution : ℝⁿ → ℝ) hΦloc (Δ f) hΔc hΔcs x
    have hT : MeasurePreserving (fun y : ℝⁿ => x - y) volume volume :=
      Measure.measurePreserving_sub_left volume x
    have hemb : MeasurableEmbedding (fun y : ℝⁿ => x - y) :=
      (Homeomorph.subLeft x).measurableEmbedding
    rw [← hT.integrable_comp_emb hemb]
    refine hpot.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [Function.comp, smul_eq_mul, sub_sub_cancel]
  obtain ⟨R, hRsub⟩ := hf_supp.isCompact.isBounded.subset_ball x
  set r := max R 1 with hrdef
  have hr0 : 0 < r := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hrR : R ≤ r := le_max_left _ _
  have htsub : tsupport f ⊆ Metric.ball x r :=
    hRsub.trans (Metric.ball_subset_ball hrR)
  have hsupp : ∀ y, r ≤ ‖y - x‖ → f y = 0 := by
    intro y hy
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have := htsub hmem
    rw [Metric.mem_ball, dist_eq_norm] at this
    linarith
  have hsuppg : ∀ y, r ≤ ‖y - x‖ → gradient f y = 0 := by
    intro y hy
    have hyn : y ∉ tsupport f := fun hmem => by
      have := htsub hmem; rw [Metric.mem_ball, dist_eq_norm] at this; linarith
    have hf0 : f =ᶠ[nhds y] 0 :=
      Filter.eventuallyEq_of_mem (isOpen_compl_iff.mpr (isClosed_tsupport f) |>.mem_nhds hyn)
        (fun z hz => image_eq_zero_of_notMem_tsupport hz)
    rw [gradient_congr hf0]
    unfold gradient; simp [fderiv_const]
  have hΔ0 : ∀ y, r ≤ ‖y - x‖ → Δ f y = 0 := by
    intro y hy
    have hyn : y ∉ tsupport f := fun hmem => by
      have := htsub hmem; rw [Metric.mem_ball, dist_eq_norm] at this; linarith
    have hf0 : f =ᶠ[nhds y] 0 :=
      Filter.eventuallyEq_of_mem (isOpen_compl_iff.mpr (isClosed_tsupport f) |>.mem_nhds hyn)
        (fun z hz => image_eq_zero_of_notMem_tsupport hz)
    rw [(laplacian_congr_nhds hf0).eq_of_nhds]; exact congr_fun laplacian_const y
  have hfull : (∫ y, fundamentalSolution (x - y) * Δ f y)
      = ∫ y in Metric.ball x r, fundamentalSolution (x - y) * Δ f y := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Metric.ball x r) (fun y hy => ?_)]
    rw [Metric.mem_ball, dist_eq_norm, not_lt] at hy
    rw [hΔ0 y hy, mul_zero]
  obtain ⟨M₀, hM₀⟩ := hΔcs.isCompact.exists_bound_of_continuousOn hΔc.continuousOn
  set M := max M₀ 0 with hMdef
  have hM0 : 0 ≤ M := le_max_right _ _
  have hMbd : ∀ y, ‖Δ f y‖ ≤ M := fun y => by
    by_cases hy : y ∈ tsupport (Δ f)
    · exact le_trans (hM₀ y hy) (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport hy, norm_zero]; exact hM0
  have hΦxint : ∀ ε : ℝ, IntegrableOn (fun y => ‖fundamentalSolution (x - y)‖)
      (Metric.ball x ε) volume := by
    intro ε
    have hT : MeasurePreserving (fun y : ℝⁿ => x - y) volume volume :=
      Measure.measurePreserving_sub_left volume x
    have hemb : MeasurableEmbedding (fun y : ℝⁿ => x - y) :=
      (Homeomorph.subLeft x).measurableEmbedding
    have h1 : IntegrableOn (fundamentalSolution : ℝⁿ → ℝ) (Metric.ball 0 ε) volume :=
      (hΦloc.integrableOn_isCompact (isCompact_closedBall 0 ε)).mono_set
        Metric.ball_subset_closedBall
    have hbase : IntegrableOn (fun z => ‖fundamentalSolution z‖) (Metric.ball 0 ε) volume := h1.norm
    have hpre : (fun y : ℝⁿ => x - y) ⁻¹' Metric.ball 0 ε = Metric.ball x ε := by
      ext y
      simp only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm, sub_zero, norm_sub_rev x y]
    rw [← hpre]
    exact (hT.integrableOn_comp_preimage hemb).mpr hbase
  have hNlim : Filter.Tendsto (fun ε => ∫ y in Metric.ball x ε, fundamentalSolution (x - y) * Δ f y)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    apply squeeze_zero_norm' (a := fun ε => M * ∫ y in Metric.ball x ε, ‖fundamentalSolution (x - y)‖)
    · filter_upwards with ε
      calc ‖∫ y in Metric.ball x ε, fundamentalSolution (x - y) * Δ f y‖
          ≤ ∫ y in Metric.ball x ε, ‖fundamentalSolution (x - y) * Δ f y‖ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ y in Metric.ball x ε, M * ‖fundamentalSolution (x - y)‖ := by
            apply setIntegral_mono_on (hg.norm.integrableOn) ((hΦxint ε).const_mul M)
              measurableSet_ball
            intro y _
            rw [norm_mul, mul_comm]
            exact mul_le_mul_of_nonneg_right (hMbd y) (norm_nonneg _)
        _ = M * ∫ y in Metric.ball x ε, ‖fundamentalSolution (x - y)‖ := integral_const_mul M _
    · simpa using (fundamentalSolution_near_integral_tendsto_zero x).const_mul M
  have key : Filter.Tendsto
      (fun _ : ℝ => ∫ y in Metric.ball x r, fundamentalSolution (x - y) * Δ f y)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (- f x)) := by
    have hRHS : Filter.Tendsto
        (fun ε => (- ∫ y in Metric.sphere x ε,
            (fundamentalSolution (y - x) * ⟪gradient f y, ‖y - x‖⁻¹ • (y - x)⟫_ℝ
             - f y * ⟪gradient fundamentalSolution (y - x), ‖y - x‖⁻¹ • (y - x)⟫_ℝ)
            ∂(μHE[n - 1] : Measure ℝⁿ))
          + ∫ y in Metric.ball x ε, fundamentalSolution (x - y) * Δ f y)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (- f x)) := by
      have := ((green_boundary_tendsto_f hn f hf hf_supp x).neg).add hNlim
      simpa using this
    refine hRHS.congr' ?_
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hr0)] with ε hε_pos hε_lt
    have hεpos : 0 < ε := hε_pos
    have hεlt : ε < r := hε_lt
    have hga := green_annulus_fund hn x f hf r ε hεpos hεlt hsupp hsuppg
    have hsub : Metric.ball x ε ⊆ Metric.ball x r := Metric.ball_subset_ball hεlt.le
    have hunion : ∫ y in Metric.ball x r, fundamentalSolution (x - y) * Δ f y
        = (∫ y in Metric.ball x ε, fundamentalSolution (x - y) * Δ f y)
          + ∫ y in Metric.ball x r \ Metric.ball x ε, fundamentalSolution (x - y) * Δ f y := by
      rw [← setIntegral_union disjoint_sdiff_self_right
        (measurableSet_ball.diff measurableSet_ball) hg.integrableOn hg.integrableOn,
        Set.union_diff_cancel hsub]
    rw [hunion, hga]; ring
  have hfinal := tendsto_nhds_unique tendsto_const_nhds key
  rw [hfull, hfinal]

/-- **Representation Formula** (Evans §2.2.4, Theorem 9): `u(x) = ∫ Φ(x−y) f(y) dy` solves
    `−Δu = f` for `n ≥ 2`. Combines Part A (`laplacian_newtonianPotential`: `Δu = ∫ Φ(x−y)·Δf`)
    with Part B (`fund_poisson_integral`: `∫ Φ(x−y)·Δf = −f(x)`). -/
theorem newtonianPotential_solves_poisson (hn : 2 ≤ n) (f : ℝⁿ → ℝ) (hf : ContDiff ℝ 2 f)
    (hf_supp : HasCompactSupport f) :
    IsPoissonSolution Set.univ f (newtonianPotential f) := by
  intro x _
  rw [laplacian_newtonianPotential f hf hf_supp x, fund_poisson_integral hn f hf hf_supp x, neg_neg]

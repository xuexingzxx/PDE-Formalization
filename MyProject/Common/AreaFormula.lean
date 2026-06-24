import Mathlib

/-!
# The area formula: linear and affine-graph cases

This file develops the first milestone toward a surface-measure / area formula in
`ℝⁿ`, working with the dimension-normalized Euclidean Hausdorff measure `μHE[d]`
(`MeasureTheory.Measure.euclideanHausdorffMeasure`), which agrees with `volume` on a
`d`-dimensional inner product space.

## Main results

* `AreaFormula.μHE_image_linear`: for an injective linear map `L : ℝᵐ → F` into a
  finite-dimensional inner product space, the `m`-dimensional Euclidean Hausdorff measure
  of `L '' A` is the Jacobian `√det(Lᵀ L)` times `volume A`. This is the load-bearing
  *linear area formula*; Mathlib only provides volume scaling for endomorphisms, so the
  higher-codimension image is handled by corestricting to `range L`, transferring through
  an orthonormal isometry, and applying `addHaar_image_linearMap`.

* `AreaFormula.μHE_graph`: the **affine graph area formula** — the `m`-dimensional measure
  of the graph of `y ↦ ⟪a, y⟫` over `A ⊆ ℝᵐ` equals `√(1 + ‖a‖²) · volume A`. The Gram
  matrix of the graph map is `1 + a aᵀ`, whose determinant is `1 + ‖a‖²`.

These are the affine pieces underlying the general (`C¹`) area formula, to be obtained by
local linearization and a covering argument.
-/

open MeasureTheory Matrix Module
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace AreaFormula

/-- Two-sided bound for the Hausdorff measure of the image under a bi-Lipschitz map: the
local squeeze underlying the linearization step of the area formula. -/
theorem hausdorffMeasure_image_bilipschitz {X Y : Type*}
    [MeasurableSpace X] [EMetricSpace X] [BorelSpace X]
    [MeasurableSpace Y] [EMetricSpace Y] [BorelSpace Y]
    {f : X → Y} {K K' : ℝ≥0} {d : ℝ}
    (hd : 0 ≤ d) (hK' : K' ≠ 0) (hL : LipschitzWith K f) (hA : AntilipschitzWith K' f)
    (s : Set X) :
    ((K' : ℝ≥0∞) ^ d)⁻¹ * μH[d] s ≤ μH[d] (f '' s)
      ∧ μH[d] (f '' s) ≤ (K : ℝ≥0∞) ^ d * μH[d] s := by
  refine ⟨?_, hL.hausdorffMeasure_image_le hd s⟩
  have h := hA.le_hausdorffMeasure_image hd s
  have hKpos : (0 : ℝ≥0∞) < (K' : ℝ≥0∞) := by exact_mod_cast hK'.bot_lt
  have htop : (K' : ℝ≥0∞) ^ d ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hd (by simp)
  have hne : (K' : ℝ≥0∞) ^ d ≠ 0 := (ENNReal.rpow_pos hKpos (by simp)).ne'
  calc ((K' : ℝ≥0∞) ^ d)⁻¹ * μH[d] s
      ≤ ((K' : ℝ≥0∞) ^ d)⁻¹ * ((K' : ℝ≥0∞) ^ d * μH[d] (f '' s)) := by gcongr
    _ = μH[d] (f '' s) := by rw [← mul_assoc, ENNReal.inv_mul_cancel hne htop, one_mul]

/-- Hausdorff measure of the universe of a subtype equals that of the set (bridges the
restricted-map domain `↥S` to `S` in the cell estimate). -/
theorem hausdorffMeasure_univ_subtype {X : Type*}
    [MeasurableSpace X] [EMetricSpace X] [BorelSpace X] {d : ℝ} (hd : 0 ≤ d) (S : Set X) :
    μH[d] (Set.univ : Set ↥S) = μH[d] S := by
  have := isometry_subtype_coe (s := S) |>.hausdorffMeasure_image (Or.inl hd) Set.univ
  rw [Subtype.coe_image_univ] at this
  exact this.symm

variable {m : ℕ} {F : Type*}
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

local notation "ℝ^" m => EuclideanSpace ℝ (Fin m)

/-- For a real endomorphism of a finite-dimensional inner product space,
`det (adjoint g) = det g` (the adjoint's matrix in an orthonormal basis is the transpose). -/
theorem det_adjoint_self {n : ℕ} (g : (ℝ^n) →ₗ[ℝ] (ℝ^n)) :
    LinearMap.det (LinearMap.adjoint g) = LinearMap.det g := by
  set v := stdOrthonormalBasis ℝ (ℝ^n)
  rw [← LinearMap.det_toMatrix v.toBasis g,
    ← LinearMap.det_toMatrix v.toBasis (LinearMap.adjoint g),
    LinearMap.toMatrix_adjoint v v g, Matrix.det_conjTranspose]
  exact star_trivial _

/-- Measure-scaling core of the area formula: the `m`-dimensional Euclidean Hausdorff measure
of the image of `A ⊆ ℝᵐ` under an injective linear map `L : ℝᵐ → F` is the Jacobian
`√det(Lᵀ L)` times the volume of `A`. -/
theorem μHE_image_linear (L : (ℝ^m) →ₗ[ℝ] F) (hL : Function.Injective L) (A : Set (ℝ^m)) :
    (μHE[m] : Measure F) (L '' A)
      = ENNReal.ofReal (Real.sqrt (LinearMap.det (LinearMap.adjoint L ∘ₗ L))) * volume A := by
  -- corestriction to the range
  set e : (ℝ^m) ≃ₗ[ℝ] ↥(LinearMap.range L) := LinearEquiv.ofInjective L hL with he
  have hrank : finrank ℝ ↥(LinearMap.range L) = m := by
    rw [← LinearEquiv.finrank_eq e, finrank_euclideanSpace_fin]
  -- a `Fin m`-indexed orthonormal basis of the range, and its isometry to ℝᵐ
  set bP : OrthonormalBasis (Fin m) ℝ ↥(LinearMap.range L) :=
    (stdOrthonormalBasis ℝ ↥(LinearMap.range L)).reindex (finCongr hrank) with hbP
  -- the automorphism φ = bP.repr ∘ e of ℝᵐ
  set φ : (ℝ^m) ≃ₗ[ℝ] (ℝ^m) := e.trans bP.repr.toLinearEquiv with hφ
  -- L '' A = subtype '' (e '' A), with subtype an isometry
  have hLcoe : (L '' A) = Subtype.val '' (e '' A) := by
    rw [Set.image_image]
    refine Set.image_congr' fun x => ?_
    simp [he, LinearEquiv.ofInjective_apply]
  calc (μHE[m] : Measure F) (L '' A)
      = (μHE[m] : Measure ↥(LinearMap.range L)) (e '' A) := by
        rw [hLcoe]; exact (isometry_subtype_coe).euclideanHausdorffMeasure_image _
    _ = (μHE[m] : Measure (ℝ^m)) (bP.repr '' (e '' A)) :=
        (bP.repr.isometry.euclideanHausdorffMeasure_image _).symm
    _ = volume (bP.repr '' (e '' A)) := by
        rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume m]
    _ = volume ((φ : (ℝ^m) → (ℝ^m)) '' A) := by
        rw [hφ]; simp [Set.image_image, LinearEquiv.trans_apply]
    _ = ENNReal.ofReal |LinearMap.det (φ : (ℝ^m) →ₗ[ℝ] (ℝ^m))| * volume A :=
        Measure.addHaar_image_linearMap volume _ A
    _ = ENNReal.ofReal (Real.sqrt (LinearMap.det (LinearMap.adjoint L ∘ₗ L))) * volume A := by
        congr 2
        -- the Gram forms of `L` and `φ` agree (`subtype` and `bP.repr` preserve inner products)
        have hgram : LinearMap.adjoint L ∘ₗ L
            = LinearMap.adjoint (φ : (ℝ^m) →ₗ[ℝ] (ℝ^m)) ∘ₗ (φ : (ℝ^m) →ₗ[ℝ] (ℝ^m)) := by
          refine LinearMap.ext fun x => ext_inner_left ℝ fun y => ?_
          rw [LinearMap.comp_apply, LinearMap.comp_apply,
            LinearMap.adjoint_inner_right, LinearMap.adjoint_inner_right]
          have hφy : (φ : (ℝ^m) →ₗ[ℝ] (ℝ^m)) y = bP.repr (e y) := rfl
          have hφx : (φ : (ℝ^m) →ₗ[ℝ] (ℝ^m)) x = bP.repr (e x) := rfl
          have hy : ((e y : ↥(LinearMap.range L)) : F) = L y := LinearEquiv.ofInjective_apply L y
          have hx : ((e x : ↥(LinearMap.range L)) : F) = L x := LinearEquiv.ofInjective_apply L x
          rw [hφy, hφx, bP.repr.inner_map_map, ← hy, ← hx]
          rfl
        -- hence `det(Lᵀ L) = (det φ)²`, and `√` of that is `|det φ|`
        have hsq : LinearMap.det (LinearMap.adjoint L ∘ₗ L)
            = (LinearMap.det (φ : (ℝ^m) →ₗ[ℝ] (ℝ^m))) ^ 2 := by
          rw [hgram, LinearMap.det_comp, det_adjoint_self, sq]
        rw [hsq, Real.sqrt_sq_eq_abs]

/-- Affine version of the linear area formula: translating the image leaves `μHE[m]`
unchanged, so an affine map `z ↦ v + L z` scales by the same Jacobian `√det(Lᵀ L)`. -/
theorem μHE_image_affine (L : (ℝ^m) →ₗ[ℝ] F) (hL : Function.Injective L) (v : F) (A : Set (ℝ^m)) :
    (μHE[m] : Measure F) ((fun z => v + L z) '' A)
      = ENNReal.ofReal (Real.sqrt (LinearMap.det (LinearMap.adjoint L ∘ₗ L))) * volume A := by
  have hiso : Isometry (fun x : F => v + x) :=
    Isometry.of_dist_eq fun x y => by simp [dist_add_left]
  have himg : (fun z => v + L z) '' A = (fun x : F => v + x) '' (L '' A) := by
    rw [Set.image_image]
  rw [himg, hiso.euclideanHausdorffMeasure_image, μHE_image_linear L hL A]

omit [MeasurableSpace F] [BorelSpace F] in
/-- An injective linear map from `ℝᵐ` into a finite-dimensional inner product space is
antilipschitz (bounded below), via a continuous left inverse. This is the lower bi-Lipschitz
bound used to control a `C¹` map by its derivative in the cell estimate. -/
theorem exists_antilipschitz_of_injective {L : (ℝ^m) →ₗ[ℝ] F} (hL : Function.Injective L) :
    ∃ K : ℝ≥0, AntilipschitzWith K L := by
  obtain ⟨g, hg⟩ := L.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hL)
  let gC : F →L[ℝ] (ℝ^m) := LinearMap.toContinuousLinearMap g
  refine ⟨‖gC‖₊, AddMonoidHomClass.antilipschitz_of_bound L fun x => ?_⟩
  have hx : x = gC (L x) := by simpa [gC] using (LinearMap.congr_fun hg x).symm
  calc ‖x‖ = ‖gC (L x)‖ := by rw [← hx]
    _ ≤ ‖gC‖₊ * ‖L x‖ := gC.le_opNorm (L x)

omit [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] in
/-- The "straightening" map `T = φ ∘ Φ_L⁻¹` (where `Φ_L x = φ x₀ + L(x - x₀)`) approximates the
identity with constant `c·K` on `Φ_L '' Q`, when `φ` approximates `L` with constant `c` on `Q`
and `L` is `K`-antilipschitz. This is the bridge that lets the bi-Lipschitz squeeze compare
`φ '' Q` to the affine `Φ_L '' Q`. -/
theorem approximatesLinearOn_comp_invFun {φ : (ℝ^m) → F} {L : (ℝ^m) →L[ℝ] F}
    {Q : Set (ℝ^m)} {c K : ℝ≥0} (hLinj : Function.Injective L) (hK : AntilipschitzWith K L)
    (happ : ApproximatesLinearOn φ L Q c) (x₀ : ℝ^m) :
    ApproximatesLinearOn (φ ∘ Function.invFun (fun x => φ x₀ + L (x - x₀)))
      (ContinuousLinearMap.id ℝ F) ((fun x => φ x₀ + L (x - x₀)) '' Q) (c * K) := by
  set Φ : (ℝ^m) → F := fun x => φ x₀ + L (x - x₀) with hΦ
  have hΦinj : Function.Injective Φ := by
    intro a b hab
    simp only [hΦ, add_right_inj] at hab
    simpa using hLinj hab
  intro p hp p' hp'
  obtain ⟨x, hx, rfl⟩ := hp
  obtain ⟨x', hx', rfl⟩ := hp'
  have hTx : (φ ∘ Function.invFun Φ) (Φ x) = φ x := by
    simp [Function.leftInverse_invFun hΦinj x]
  have hTx' : (φ ∘ Function.invFun Φ) (Φ x') = φ x' := by
    simp [Function.leftInverse_invFun hΦinj x']
  have hΦsub : Φ x - Φ x' = L (x - x') := by
    simp only [hΦ]; rw [add_sub_add_left_eq_sub, ← map_sub]; congr 1; abel
  rw [hTx, hTx', ContinuousLinearMap.id_apply, hΦsub]
  calc ‖φ x - φ x' - L (x - x')‖
      ≤ c * ‖x - x'‖ := happ x hx x' hx'
    _ ≤ c * (K * ‖L (x - x')‖) := by
        gcongr
        have := hK.le_mul_dist x x'
        simpa [dist_eq_norm, map_sub] using this
    _ = (c * K : ℝ≥0) * ‖L (x - x')‖ := by push_cast; ring

/-- The linear part of an affine graph map: `y ↦ (y, ⟪a, y⟫)` into the `L²` product. -/
def graphMap (a : ℝ^m) : (ℝ^m) →ₗ[ℝ] WithLp 2 ((ℝ^m) × ℝ) :=
  (WithLp.linearEquiv 2 ℝ ((ℝ^m) × ℝ)).symm.toLinearMap ∘ₗ
    (LinearMap.id.prod (innerSL ℝ a).toLinearMap)

lemma graph_injective (a : ℝ^m) : Function.Injective (graphMap a) := by
  intro y z h
  have h1 := congrArg (fun w => (WithLp.linearEquiv 2 ℝ ((ℝ^m) × ℝ) w).1) h
  simpa [graphMap] using h1

/-- The Gram determinant of the affine graph map is `1 + ‖a‖²`. -/
theorem graph_gram_det (a : ℝ^m) :
    LinearMap.det (LinearMap.adjoint (graphMap a) ∘ₗ graphMap a) = 1 + ‖a‖ ^ 2 := by
  have hcoe : ∀ y : ℝ^m, (graphMap a y).ofLp = (y, (inner ℝ a y : ℝ)) := fun _ => rfl
  -- the operator is `id + a⊗a`
  have hT : LinearMap.adjoint (graphMap a) ∘ₗ graphMap a
      = LinearMap.id + ((innerSL ℝ a).smulRight a : (ℝ^m) →L[ℝ] (ℝ^m)).toLinearMap := by
    refine LinearMap.ext fun x => ext_inner_left ℝ fun z => ?_
    rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right, WithLp.prod_inner_apply,
      hcoe, hcoe]
    simp only [LinearMap.add_apply, LinearMap.id_apply, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_add_right,
      real_inner_smul_right]
    change inner ℝ z x + inner ℝ a x * inner ℝ a z = inner ℝ z x + inner ℝ a x * inner ℝ z a
    rw [real_inner_comm z a]
  set b := EuclideanSpace.basisFun (Fin m) ℝ with hb
  have hinner : ∀ j, (inner ℝ a (EuclideanSpace.basisFun (Fin m) ℝ j) : ℝ) = a j :=
    fun j => EuclideanSpace.inner_basisFun_real (x := a) (i := j)
  -- the matrix of `id + a⊗a` is `1 + a aᵀ`
  have hmat : LinearMap.toMatrix b.toBasis b.toBasis (LinearMap.adjoint (graphMap a) ∘ₗ graphMap a)
      = 1 + Matrix.replicateCol (Fin 1) (⇑a) * Matrix.replicateRow (Fin 1) (⇑a) := by
    rw [hT, map_add, LinearMap.toMatrix_id]
    congr 1
    ext i j
    rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
      OrthonormalBasis.coe_toBasis_repr_apply]
    simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.smulRight_apply,
      innerSL_apply_apply, hb, hinner, map_smul, PiLp.smul_apply, smul_eq_mul,
      EuclideanSpace.basisFun_repr, Matrix.mul_apply, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin,
      Matrix.replicateCol_apply, Matrix.replicateRow_apply]
    ring
  refine (LinearMap.det_toMatrix b.toBasis _).symm.trans ?_
  rw [hmat]
  refine (Matrix.det_one_add_replicateCol_mul_replicateRow _ _).trans ?_
  congr 1
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  simp [dotProduct, Real.norm_eq_abs, pow_two]

/-- **Affine graph area formula.** The `m`-dimensional Euclidean Hausdorff measure of the
graph of `y ↦ ⟪a, y⟫` over `A ⊆ ℝᵐ` equals `√(1 + ‖a‖²) · volume A`. -/
theorem μHE_graph (a : ℝ^m) (A : Set (ℝ^m)) :
    (μHE[m] : Measure (WithLp 2 ((ℝ^m) × ℝ))) (graphMap a '' A)
      = ENNReal.ofReal (Real.sqrt (1 + ‖a‖ ^ 2)) * volume A := by
  rw [μHE_image_linear (graphMap a) (graph_injective a) A, graph_gram_det a]

/-! ### The `C¹` graph: integrand regularity

Towards the general `C¹` graph area formula `μHE[m](Φ''A) = ∫_A √(1 + ‖∇g‖²)`, where
`Φ y = (y, g y)`. The right-hand integrand must be continuous (hence measurable, and usable
in the covering/Riemann-sum step). -/

/-- The gradient of a `C¹` function is continuous. -/
theorem continuous_gradient {g : (ℝ^m) → ℝ} (hg : ContDiff ℝ 1 g) :
    Continuous (gradient g) :=
  (InnerProductSpace.toDual ℝ (ℝ^m)).symm.continuous.comp (hg.continuous_fderiv (by norm_num))

/-- The area integrand `y ↦ √(1 + ‖∇g(y)‖²)` of a `C¹` function is continuous. -/
theorem continuous_graph_integrand {g : (ℝ^m) → ℝ} (hg : ContDiff ℝ 1 g) :
    Continuous (fun y => Real.sqrt (1 + ‖gradient g y‖ ^ 2)) :=
  Continuous.sqrt (continuous_const.add ((continuous_gradient hg).norm.pow 2))

end AreaFormula

end

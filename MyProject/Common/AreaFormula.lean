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

open MeasureTheory Matrix Module Filter Topology
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

/-- The Jacobian `√det(Mᵀ M)` of a linear map `M : ℝᵐ → F`. By `gram_det_nonneg` the argument
of the square root is nonnegative, so this is a faithful square root; it is the local volume-
scaling factor in the area formula. -/
def jacobian (M : (ℝ^m) →L[ℝ] F) : ℝ :=
  Real.sqrt (LinearMap.det (LinearMap.adjoint M.toLinearMap ∘ₗ M.toLinearMap))

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

omit [MeasurableSpace F] [BorelSpace F] in
/-- The Gram determinant `det(Lᵀ L)` is nonnegative: in orthonormal bases `Lᵀ L` has matrix
`Gᴴ G` (with `G` the matrix of `L`), which is positive semidefinite. This makes the Jacobian
`√det(Lᵀ L)` a faithful (non-truncated) square root. -/
theorem gram_det_nonneg (L : (ℝ^m) →ₗ[ℝ] F) :
    0 ≤ LinearMap.det (LinearMap.adjoint L ∘ₗ L) := by
  set b := stdOrthonormalBasis ℝ (ℝ^m) with hb
  set bF := stdOrthonormalBasis ℝ F with hbF
  rw [← LinearMap.det_toMatrix b.toBasis]
  set G := LinearMap.toMatrix b.toBasis bF.toBasis L with hG
  have hmat : LinearMap.toMatrix b.toBasis b.toBasis (LinearMap.adjoint L ∘ₗ L) = Gᴴ * G := by
    rw [LinearMap.toMatrix_comp b.toBasis bF.toBasis b.toBasis,
      LinearMap.toMatrix_adjoint b bF L, hG]
  rw [hmat]
  exact (Matrix.posSemidef_conjTranspose_mul_self G).det_nonneg

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

set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- **Cell estimate.** If `φ` approximates the injective `K`-antilipschitz linear map `L` with
constant `c` on `Q` (and `c·K < 1`), then `μHE[m](φ '' Q)` is squeezed between
`(1 ∓ cK)^m · √det(Lᵀ L) · volume Q`. The straightening map `T = φ ∘ Φ_L⁻¹` is near-identity
bi-Lipschitz, so the squeeze compares `φ '' Q` to the affine image whose measure is the
Jacobian (milestone 1). -/
theorem cell_estimate [Nontrivial F] {φ : (ℝ^m) → F} {L : (ℝ^m) →L[ℝ] F}
    {Q : Set (ℝ^m)} {c K : ℝ≥0} (hLinj : Function.Injective L)
    (hK : AntilipschitzWith K L) (happ : ApproximatesLinearOn φ L Q c)
    (hcK : c * K < 1) (x₀ : ℝ^m) :
    (μHE[m] : Measure F) (φ '' Q)
        ≤ ((1 + c * K : ℝ≥0) : ℝ≥0∞) ^ (m : ℝ) *
          (ENNReal.ofReal (Real.sqrt (LinearMap.det (LinearMap.adjoint L.toLinearMap ∘ₗ L.toLinearMap)))
            * volume Q)
      ∧ ((1 - c * K : ℝ≥0) : ℝ≥0∞) ^ (m : ℝ) *
          (ENNReal.ofReal (Real.sqrt (LinearMap.det (LinearMap.adjoint L.toLinearMap ∘ₗ L.toLinearMap)))
            * volume Q)
        ≤ (μHE[m] : Measure F) (φ '' Q) := by
  classical
  set Φ : (ℝ^m) → F := fun x => φ x₀ + L (x - x₀) with hΦ
  set T : F → F := φ ∘ Function.invFun Φ with hT
  have hΦinj : Function.Injective Φ := by
    intro a b hab
    simp only [hΦ, add_right_inj] at hab
    simpa using hLinj hab
  have hTΦ : ∀ x, T (Φ x) = φ x := fun x => by
    simp [hT, Function.leftInverse_invFun hΦinj x]
  have happT : ApproximatesLinearOn T (ContinuousLinearMap.id ℝ F) (Φ '' Q) (c * K) :=
    approximatesLinearOn_comp_invFun hLinj hK happ x₀
  have happT' : ApproximatesLinearOn T ((ContinuousLinearEquiv.refl ℝ F) : F →L[ℝ] F)
      (Φ '' Q) (c * K) := by rwa [ContinuousLinearEquiv.coe_refl]
  have hN : ‖((ContinuousLinearEquiv.refl ℝ F).symm : F →L[ℝ] F)‖₊ = 1 := by
    simp [ContinuousLinearMap.nnnorm_id]
  have hLipT : LipschitzWith (1 + c * K) ((Φ '' Q).restrict T) := by
    have := happT.lipschitz
    simpa [ContinuousLinearMap.nnnorm_id] using this
  have hAntiT : AntilipschitzWith (1 - c * K)⁻¹ ((Φ '' Q).restrict T) := by
    have hcK' : c * K < ‖((ContinuousLinearEquiv.refl ℝ F).symm : F →L[ℝ] F)‖₊⁻¹ := by
      rw [hN, inv_one]; exact hcK
    have := happT'.antilipschitz (Or.inr hcK')
    rwa [hN, inv_one] at this
  have himg : ((Φ '' Q).restrict T) '' Set.univ = φ '' Q := by
    rw [Set.image_univ, Set.range_restrict, Set.image_image]
    simp only [hTΦ]
  -- raw Hausdorff squeeze on the restriction
  have hne : (1 - c * K : ℝ≥0) ≠ 0 := (tsub_pos_of_lt hcK).ne'
  have hK'ne : (1 - c * K : ℝ≥0)⁻¹ ≠ 0 := inv_ne_zero hne
  obtain ⟨hμlo, hμhi⟩ :=
    hausdorffMeasure_image_bilipschitz (d := (m : ℝ)) (by positivity) hK'ne hLipT hAntiT Set.univ
  rw [himg, hausdorffMeasure_univ_subtype (by positivity) (Φ '' Q)] at hμlo hμhi
  -- scale μH to μHE (same dimension-only factor on every set)
  set c₀ := Measure.addHaarScalarFactor
    (volume : Measure (EuclideanSpace ℝ (Fin m))) μH[(m : ℝ)] with hc₀
  have hscale : ∀ S : Set F, (μHE[m] : Measure F) S = c₀ * μH[(m : ℝ)] S := fun S => by
    rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply]; rfl
  have hcoeinv : (((1 - c * K : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) ^ (m : ℝ)
      = (((1 - c * K : ℝ≥0) : ℝ≥0∞) ^ (m : ℝ))⁻¹ := by
    rw [ENNReal.coe_inv hne, ENNReal.inv_rpow]
  -- the affine image carries the Jacobian √det(Lᵀ L)
  have haff : (μHE[m] : Measure F) (Φ '' Q)
      = ENNReal.ofReal (Real.sqrt (LinearMap.det (LinearMap.adjoint L.toLinearMap ∘ₗ L.toLinearMap)))
        * volume Q := by
    have hΦeq : Φ '' Q = (fun z => (φ x₀ - L x₀) + L.toLinearMap z) '' Q := by
      apply Set.image_congr'; intro x
      simp only [hΦ, ContinuousLinearMap.coe_coe, map_sub]; abel
    rw [hΦeq, μHE_image_affine L.toLinearMap hLinj _ Q]
  refine ⟨?_, ?_⟩
  · calc (μHE[m] : Measure F) (φ '' Q) = c₀ * μH[(m : ℝ)] (φ '' Q) := hscale _
      _ ≤ c₀ * (((1 + c * K : ℝ≥0) : ℝ≥0∞) ^ (m : ℝ) * μH[(m : ℝ)] (Φ '' Q)) := by gcongr
      _ = ((1 + c * K : ℝ≥0) : ℝ≥0∞) ^ (m : ℝ) * (c₀ * μH[(m : ℝ)] (Φ '' Q)) := by ring
      _ = ((1 + c * K : ℝ≥0) : ℝ≥0∞) ^ (m : ℝ) * (μHE[m] : Measure F) (Φ '' Q) := by
          rw [← hscale]
      _ = _ := by rw [haff]
  · have hlo' : ((1 - c * K : ℝ≥0) : ℝ≥0∞) ^ (m : ℝ) * μH[(m : ℝ)] (Φ '' Q)
        ≤ μH[(m : ℝ)] (φ '' Q) := by
      rw [hcoeinv, inv_inv] at hμlo; exact hμlo
    calc ((1 - c * K : ℝ≥0) : ℝ≥0∞) ^ (m : ℝ) *
          (ENNReal.ofReal (Real.sqrt (LinearMap.det (LinearMap.adjoint L.toLinearMap ∘ₗ L.toLinearMap)))
            * volume Q)
        = ((1 - c * K : ℝ≥0) : ℝ≥0∞) ^ (m : ℝ) * (μHE[m] : Measure F) (Φ '' Q) := by rw [haff]
      _ = c₀ * (((1 - c * K : ℝ≥0) : ℝ≥0∞) ^ (m : ℝ) * μH[(m : ℝ)] (Φ '' Q)) := by
          rw [hscale]; ring
      _ ≤ c₀ * μH[(m : ℝ)] (φ '' Q) := by gcongr
      _ = (μHE[m] : Measure F) (φ '' Q) := (hscale _).symm

set_option linter.style.longLine false in
/-- **Per-linearization cell bound.** For an injective linear map `A`, there is a tolerance
`δ > 0` such that any map `g` approximating `A` to within `δ` on a set `t` expands the
`m`-dimensional measure by at most the Jacobian plus `ε`:
`μHE[m](g '' t) ≤ (√det(Aᵀ A) + ε) · vol t`. This is `cell_estimate` with the multiplicative
factor `(1 + δK)^m` absorbed into `ε` by choosing `δ` small — the analogue of Mathlib's
`addHaar_image_le_mul_of_det_lt` and the per-cell input to the covering step of the area formula. -/
theorem exists_delta_cell_bound [Nontrivial F] {A : (ℝ^m) →L[ℝ] F}
    (hAinj : Function.Injective A) {ε : ℝ≥0} (hε : 0 < ε) :
    ∃ δ : ℝ≥0, 0 < δ ∧ ∀ (t : Set (ℝ^m)) (g : (ℝ^m) → F),
      ApproximatesLinearOn g A t δ →
        (μHE[m] : Measure F) (g '' t) ≤ (ENNReal.ofReal (jacobian A) + ε) * volume t := by
  obtain ⟨K, hK⟩ := exists_antilipschitz_of_injective (L := A.toLinearMap) hAinj
  set J : ℝ := jacobian A with hJdef
  have hJnn : 0 ≤ J := Real.sqrt_nonneg _
  -- choose a real `δ` making `(1 + δK)^m · J < J + ε` and `δK < 1`
  have hcont : ContinuousAt (fun δ : ℝ => (1 + δ * (K : ℝ)) ^ m * J) 0 := by fun_prop
  have hlt : (fun δ : ℝ => (1 + δ * (K : ℝ)) ^ m * J) 0 < J + ε := by
    simp only [zero_mul, add_zero, one_pow, one_mul]
    have : (0 : ℝ) < ε := by exact_mod_cast hε
    linarith
  have hcontK : ContinuousAt (fun δ : ℝ => δ * (K : ℝ)) 0 := by fun_prop
  have hltK : (fun δ : ℝ => δ * (K : ℝ)) 0 < 1 := by simp
  have e1 : ∀ᶠ δ in 𝓝[>] (0:ℝ), (1 + δ * (K : ℝ)) ^ m * J < J + ε :=
    (hcont.eventually_lt_const hlt).filter_mono nhdsWithin_le_nhds
  have e2 : ∀ᶠ δ in 𝓝[>] (0:ℝ), δ * (K : ℝ) < 1 :=
    (hcontK.eventually_lt_const hltK).filter_mono nhdsWithin_le_nhds
  have e3 : ∀ᶠ δ in 𝓝[>] (0:ℝ), (0:ℝ) < δ := eventually_mem_nhdsWithin.mono fun x hx => hx
  obtain ⟨δ, hδlt, hδK, hδpos⟩ := (e1.and (e2.and e3)).exists
  refine ⟨δ.toNNReal, by simpa using hδpos, fun t g hg => ?_⟩
  -- apply the cell estimate with `c = δ`, base point `0`
  have hcK : (δ.toNNReal) * K < 1 := by
    rw [← NNReal.coe_lt_coe]; push_cast
    rw [Real.coe_toNNReal δ hδpos.le]; exact hδK
  obtain ⟨hup, -⟩ := cell_estimate hAinj hK hg hcK (0 : ℝ^m)
  refine hup.trans ?_
  -- absorb the `(1 + δK)^m` factor into `ε`
  have hfac : ((1 + δ.toNNReal * K : ℝ≥0) : ℝ≥0∞) ^ (m : ℝ) * ENNReal.ofReal J
      ≤ ENNReal.ofReal J + ε := by
    have hpow : ((1 + δ.toNNReal * K : ℝ≥0) : ℝ≥0∞) ^ (m : ℝ)
        = ((1 + δ.toNNReal * K : ℝ≥0) ^ m : ℝ≥0) := by
      rw [ENNReal.rpow_natCast]; push_cast; ring_nf
    rw [hpow, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
    calc ENNReal.ofReal (((1 + δ.toNNReal * K : ℝ≥0) ^ m : ℝ≥0) * J)
        ≤ ENNReal.ofReal (J + ε) := by
          apply ENNReal.ofReal_le_ofReal
          have hcast : ((1 + δ.toNNReal * K : ℝ≥0) ^ m : ℝ) = (1 + δ * K) ^ m := by
            push_cast; rw [Real.coe_toNNReal δ hδpos.le]
          rw [show (((1 + δ.toNNReal * K : ℝ≥0) ^ m : ℝ≥0) : ℝ) = (1 + δ * K)^m from hcast]
          exact hδlt.le
      _ = ENNReal.ofReal J + ε := by
          rw [ENNReal.ofReal_add hJnn (by positivity), ENNReal.ofReal_coe_nnreal]
  calc ((1 + δ.toNNReal * K : ℝ≥0) : ℝ≥0∞) ^ (m : ℝ) * (ENNReal.ofReal J * volume t)
      = (((1 + δ.toNNReal * K : ℝ≥0) : ℝ≥0∞) ^ (m : ℝ) * ENNReal.ofReal J) * volume t := by ring
    _ ≤ (ENNReal.ofReal J + ε) * volume t := by gcongr

set_option linter.unusedSectionVars false in
/-- For an injective continuous `φ`, the measure of `φ '' A` decomposes as a sum over a measurable
partition of `A`. Continuous injective images of Borel sets are Borel (Lusin–Souslin), and
injectivity makes the pieces disjoint — so `measure_iUnion` applies. This turns the area formula
into a sum over the cells produced by the `ApproximatesLinearOn` partition. -/
theorem measure_image_tsum_of_injOn {φ : (ℝ^m) → F} (hφc : Continuous φ) {A : Set (ℝ^m)}
    (hA : MeasurableSet A) (hφinj : Set.InjOn φ A) {t : ℕ → Set (ℝ^m)}
    (htd : Pairwise (Function.onFun Disjoint t)) (htm : ∀ n, MeasurableSet (t n))
    (hAt : A ⊆ ⋃ n, t n) :
    (μHE[m] : Measure F) (φ '' A) = ∑' n, (μHE[m] : Measure F) (φ '' (A ∩ t n)) := by
  have hAeq : A = ⋃ n, A ∩ t n := by
    rw [← Set.inter_iUnion, Set.inter_eq_left.mpr hAt]
  have himg : φ '' A = ⋃ n, φ '' (A ∩ t n) := by
    conv_lhs => rw [hAeq]
    rw [Set.image_iUnion]
  rw [himg, measure_iUnion ?_ ?_]
  · intro i j hij
    simp only [Function.onFun]
    rw [Set.disjoint_iff_inter_eq_empty]
    ext y
    simp only [Set.mem_inter_iff, Set.mem_image, Set.mem_empty_iff_false, iff_false, not_and]
    rintro ⟨x₁, ⟨hx₁A, hx₁t⟩, rfl⟩ ⟨x₂, ⟨hx₂A, hx₂t⟩, hx₂⟩
    have hx : x₁ = x₂ := hφinj hx₁A hx₂A hx₂.symm
    subst hx
    exact (htd hij).le_bot ⟨hx₁t, hx₂t⟩
  · intro n
    exact (hA.inter (htm n)).image_of_continuousOn_injOn hφc.continuousOn
      (hφinj.mono Set.inter_subset_left)

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

omit [MeasurableSpace F] [BorelSpace F] in
/-- The general area integrand `M ↦ √det(Mᵀ M)` is a continuous function of the linear map.
Composed with a continuous derivative `y ↦ Dφ(y)`, this gives a continuous (hence measurable)
integrand `y ↦ √det(Dφ(y)ᵀ Dφ(y))` for the `C¹` area formula. -/
theorem continuous_jacobian : Continuous (jacobian : ((ℝ^m) →L[ℝ] F) → ℝ) := by
  unfold jacobian
  have hbridge : ∀ M : (ℝ^m) →L[ℝ] F,
      LinearMap.det (LinearMap.adjoint M.toLinearMap ∘ₗ M.toLinearMap)
        = ContinuousLinearMap.det (ContinuousLinearMap.adjoint M ∘L M) := fun _ => rfl
  simp_rw [hbridge]
  refine Real.continuous_sqrt.comp (ContinuousLinearMap.continuous_det.comp ?_)
  have hcomp : Continuous fun p : (F →L[ℝ] (ℝ^m)) × ((ℝ^m) →L[ℝ] F) => p.1.comp p.2 :=
    isBoundedBilinearMap_comp.continuous
  exact hcomp.comp ((ContinuousLinearMap.adjoint (𝕜 := ℝ)).continuous.prodMk continuous_id)

end AreaFormula

end

import Mathlib
import MyProject.Common.Calculus

/-!
# The area formula

The `m`-dimensional surface area of the image of a `C¹` map. Throughout, `F` is a
finite-dimensional real inner product space and surface measure is the dimension-normalized
Euclidean Hausdorff measure `μHE[d]` (`MeasureTheory.Measure.euclideanHausdorffMeasure`), which
agrees with `volume` on a `d`-dimensional inner product space. The local volume-scaling factor is
the **Jacobian** `jacobian M = √det(Mᵀ M)` of a linear map `M : ℝᵐ → F`.

## Main results

* `AreaFormula.area_formula`: for a `C¹` immersion `φ : ℝᵐ → F` (derivative `φ'` injective at every
  point of `A`) that is injective on a measurable set `A`,
  `μHE[m](φ '' A) = ∫_A √det(Dφ(x)ᵀ Dφ(x)) dx`.

* `AreaFormula.lintegral_image_jacobian_mul`: the change-of-variables / surface-integral form,
  `∫_{φ''A} f dμHE = ∫_A f(φ x)·√det(DφᵀDφ) dx` for measurable `f`.

* `AreaFormula.area_formula_graph` and `AreaFormula.lintegral_image_graph_mul`: the concrete graph
  case `Φ y = (y, g y)` for `g : ℝᵐ → ℝ` of class `C¹`, giving `μHE[m](Φ '' A) = ∫_A √(1 + ‖∇g‖²)`
  and `∫_{Φ''A} f dμHE = ∫_A f(x, g x)·√(1 + ‖∇g x‖²) dx`.

* `AreaFormula.μHE_image_linear` / `AreaFormula.μHE_graph`: the linear and affine-graph base cases.

## Proof architecture

The proof mirrors Mathlib's full-dimensional change-of-variables (`MeasureTheory/Function/
Jacobian.lean`), with `μHE[m]` / `√det(DφᵀDφ)` in place of Haar measure / `|det Dφ|`:

1. **Linear case** (`μHE_image_linear`): Mathlib only scales volume for endomorphisms, so a
   higher-codimension image is handled by corestricting to `range L`, transferring through an
   orthonormal isometry, then applying `addHaar_image_linearMap`.
2. **Local linearization** (`cell_estimate`): a map approximating an injective linear `L` to within
   `c` on a set expands `μHE[m]` by a factor in `[(1-cK)^m, (1+cK)^m]·√det(LᵀL)`, via a bi-Lipschitz
   squeeze against the affine image.
3. **Covering** (`exists_delta_cell_bound(_lower)` + Mathlib's `ApproximatesLinearOn` partition):
   sum the per-cell bounds and let the tolerance `→ 0`, using the a.e. derivative bound
   `approximatesLinearOn_norm_fderiv_sub_le` (a codomain-`F` port of Mathlib's endomorphism-only
   version) to identify the linearizations with `Dφ`. Injectivity of `φ` makes the lower
   direction's cell images disjoint.
4. **Integral form**: the measure identity gives a pushforward of measures
   (`map_withDensity_jacobian`), whence the change-of-variables formula.
-/

open MeasureTheory MeasureTheory.Measure Matrix Module Filter Topology Metric Set Asymptotics
open scoped ENNReal NNReal RealInnerProductSpace Pointwise Manifold

noncomputable section

namespace AreaFormula

/-! ### Hausdorff-measure preliminaries -/

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

/-! ### The Jacobian and the linear area formula -/

/-- The Jacobian `√det(Mᵀ M)` of a linear map `M : ℝᵐ → F`. By `gram_det_nonneg` the argument
of the square root is nonnegative, so this is a faithful square root; it is the local volume-
scaling factor in the area formula. -/
def jacobian (M : (ℝ^m) →L[ℝ] F) : ℝ :=
  Real.sqrt (LinearMap.det (LinearMap.adjoint M.toLinearMap ∘ₗ M.toLinearMap))

omit [MeasurableSpace F] [BorelSpace F] in
/-- The Jacobian is nonnegative (it is a square root). -/
theorem jacobian_nonneg (M : (ℝ^m) →L[ℝ] F) : 0 ≤ jacobian M := Real.sqrt_nonneg _

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

/-! ### Local linearization: the cell estimate -/

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
    simp only [hΦ] at hab
    simpa using hLinj (add_left_cancel hab)
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
    simp only [hΦ] at hab
    simpa using hLinj (add_left_cancel hab)
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
/-- **Per-linearization lower cell bound.** For an injective linear map `A` and `ε>0`, a tolerance
`δ>0` such that any `g` approximating `A` within `δ` on `t` has
`(√det(Aᵀ A))·vol t ≤ μHE[m](g''t) + ε·vol t`. This is `cell_estimate`'s lower inequality with the
`(1 - δK)^m` factor absorbed into `ε`; the per-cell input to the lower (`∫ ≤ μHE`) direction. -/
theorem exists_delta_cell_bound_lower [Nontrivial F] {A : (ℝ^m) →L[ℝ] F}
    (hAinj : Function.Injective A) {ε : ℝ≥0} (hε : 0 < ε) :
    ∃ δ : ℝ≥0, 0 < δ ∧ ∀ (t : Set (ℝ^m)) (g : (ℝ^m) → F),
      ApproximatesLinearOn g A t δ →
        ENNReal.ofReal (jacobian A) * volume t
          ≤ (μHE[m] : Measure F) (g '' t) + ε * volume t := by
  obtain ⟨K, hK⟩ := exists_antilipschitz_of_injective (L := A.toLinearMap) hAinj
  set J : ℝ := jacobian A with hJdef
  have hJnn : 0 ≤ J := jacobian_nonneg A
  -- choose a real δ making `J ≤ (1 - δK)^m · J + ε` and `δK < 1`
  have hcont : ContinuousAt (fun δ : ℝ => (1 - δ * (K : ℝ)) ^ m * J + ε) 0 := by fun_prop
  have hgt : J < (fun δ : ℝ => (1 - δ * (K : ℝ)) ^ m * J + ε) 0 := by
    simp only [zero_mul, sub_zero, one_pow, one_mul]
    have : (0 : ℝ) < ε := by exact_mod_cast hε
    linarith
  have hcontK : ContinuousAt (fun δ : ℝ => δ * (K : ℝ)) 0 := by fun_prop
  have hltK : (fun δ : ℝ => δ * (K : ℝ)) 0 < 1 := by simp
  have e1 : ∀ᶠ δ in 𝓝[>] (0:ℝ), J < (1 - δ * (K : ℝ)) ^ m * J + ε :=
    (hcont.eventually_const_lt hgt).filter_mono nhdsWithin_le_nhds
  have e2 : ∀ᶠ δ in 𝓝[>] (0:ℝ), δ * (K : ℝ) < 1 :=
    (hcontK.eventually_lt_const hltK).filter_mono nhdsWithin_le_nhds
  have e3 : ∀ᶠ δ in 𝓝[>] (0:ℝ), (0:ℝ) < δ := eventually_mem_nhdsWithin.mono fun x hx => hx
  obtain ⟨δ, hδlt, hδK, hδpos⟩ := (e1.and (e2.and e3)).exists
  refine ⟨δ.toNNReal, by simpa using hδpos, fun t g hg => ?_⟩
  have hcK : (δ.toNNReal) * K < 1 := by
    rw [← NNReal.coe_lt_coe]; push_cast
    rw [Real.coe_toNNReal δ hδpos.le]; exact hδK
  obtain ⟨-, hlow⟩ := cell_estimate hAinj hK hg hcK (0 : ℝ^m)
  have h1δK : (0 : ℝ) ≤ 1 - δ * K := by linarith
  have hsub : ((1 - δ.toNNReal * K : ℝ≥0) : ℝ) = 1 - δ * K := by
    rw [NNReal.coe_sub hcK.le, NNReal.coe_one, NNReal.coe_mul, Real.coe_toNNReal δ hδpos.le]
  have hpow : ((1 - δ.toNNReal * K : ℝ≥0) : ℝ≥0∞) ^ (m : ℝ)
      = ENNReal.ofReal ((1 - δ * K) ^ m) := by
    rw [ENNReal.rpow_natCast, ← ENNReal.ofReal_coe_nnreal,
      ← ENNReal.ofReal_pow (NNReal.coe_nonneg _), hsub]
  have hbound : ENNReal.ofReal J
      ≤ ((1 - δ.toNNReal * K : ℝ≥0) : ℝ≥0∞) ^ (m : ℝ) * ENNReal.ofReal J + ε := by
    rw [hpow, ← ENNReal.ofReal_mul (pow_nonneg h1δK m)]
    calc ENNReal.ofReal J
        ≤ ENNReal.ofReal ((1 - δ * K) ^ m * J + ε) := ENNReal.ofReal_le_ofReal hδlt.le
      _ = ENNReal.ofReal ((1 - δ * K) ^ m * J) + ε := by
          rw [ENNReal.ofReal_add (mul_nonneg (pow_nonneg h1δK m) hJnn) (by positivity),
            ENNReal.ofReal_coe_nnreal]
  calc ENNReal.ofReal J * volume t
      ≤ (((1 - δ.toNNReal * K : ℝ≥0) : ℝ≥0∞) ^ (m : ℝ) * ENNReal.ofReal J + ε) * volume t := by
        gcongr
    _ = ((1 - δ.toNNReal * K : ℝ≥0) : ℝ≥0∞) ^ (m : ℝ) * (ENNReal.ofReal J * volume t)
          + ε * volume t := by ring
    _ ≤ (μHE[m] : Measure F) (g '' t) + ε * volume t := by gcongr; exact hlow

/-! ### Covering tools -/

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

set_option linter.unusedSectionVars false in
/-- The a.e. derivative bound: if `φ` approximates the linear map `A` to within `δ` on a
measurable set `s`, then `‖Dφ(x) - A‖ ≤ δ` for almost every `x ∈ s`. This is the codomain-`F`
generalization of Mathlib's `ApproximatesLinearOn.norm_fderiv_sub_le` (stated there only for
endomorphisms); the proof is the same Lebesgue-density argument on the domain `ℝᵐ`. It lets the
discrete linearizations `A n` of the covering be compared to the pointwise derivative `Dφ`. -/
theorem approximatesLinearOn_norm_fderiv_sub_le {φ : (ℝ^m) → F} {A : (ℝ^m) →L[ℝ] F} {δ : ℝ≥0}
    {s : Set (ℝ^m)} (hf : ApproximatesLinearOn φ A s δ) (hs : MeasurableSet s)
    (φ' : (ℝ^m) → (ℝ^m) →L[ℝ] F) (hf' : ∀ x ∈ s, HasFDerivWithinAt φ (φ' x) s x) :
    ∀ᵐ x ∂(volume : Measure (ℝ^m)).restrict s, ‖φ' x - A‖₊ ≤ δ := by
  filter_upwards [Besicovitch.ae_tendsto_measure_inter_div (volume : Measure (ℝ^m)) s,
    ae_restrict_mem hs]
  intro x hx xs
  apply ContinuousLinearMap.opNorm_le_bound _ δ.2 fun z => ?_
  suffices H : ∀ ε, 0 < ε → ‖(φ' x - A) z‖ ≤ (δ + ε) * (‖z‖ + ε) + ‖φ' x - A‖ * ε by
    have :
      Tendsto (fun ε : ℝ => ((δ : ℝ) + ε) * (‖z‖ + ε) + ‖φ' x - A‖ * ε) (𝓝[>] 0)
        (𝓝 ((δ + 0) * (‖z‖ + 0) + ‖φ' x - A‖ * 0)) :=
      Tendsto.mono_left (Continuous.tendsto (by fun_prop) 0) nhdsWithin_le_nhds
    simp only [add_zero, mul_zero] at this
    apply le_of_tendsto_of_tendsto tendsto_const_nhds this
    filter_upwards [self_mem_nhdsWithin]
    exact H
  intro ε εpos
  have B₁ : ∀ᶠ r in 𝓝[>] (0 : ℝ), (s ∩ ({x} + r • closedBall z ε)).Nonempty :=
    eventually_nonempty_inter_smul_of_density_one volume s x hx _ measurableSet_closedBall
      (measure_closedBall_pos volume z εpos).ne'
  obtain ⟨ρ, ρpos, hρ⟩ :
      ∃ ρ > 0, ball x ρ ∩ s ⊆ {y : ℝ^m | ‖φ y - φ x - (φ' x) (y - x)‖ ≤ ε * ‖y - x‖} :=
    mem_nhdsWithin_iff.1 ((hf' x xs).isLittleO.def εpos)
  have B₂ : ∀ᶠ r in 𝓝[>] (0 : ℝ), {x} + r • closedBall z ε ⊆ ball x ρ := by
    apply nhdsWithin_le_nhds
    exact eventually_singleton_add_smul_subset isBounded_closedBall (ball_mem_nhds x ρpos)
  obtain ⟨r, ⟨y, ⟨ys, hy⟩⟩, rρ, rpos⟩ :
      ∃ r : ℝ,
        (s ∩ ({x} + r • closedBall z ε)).Nonempty ∧
          {x} + r • closedBall z ε ⊆ ball x ρ ∧ 0 < r :=
    (B₁.and (B₂.and self_mem_nhdsWithin)).exists
  obtain ⟨a, az, ya⟩ : ∃ a, a ∈ closedBall z ε ∧ y = x + r • a := by
    simp only [mem_smul_set, image_add_left, mem_preimage, singleton_add] at hy
    rcases hy with ⟨a, az, ha⟩
    exact ⟨a, az, by simp only [ha, add_neg_cancel_left]⟩
  have norm_a : ‖a‖ ≤ ‖z‖ + ε :=
    calc
      ‖a‖ = ‖z + (a - z)‖ := by simp only [add_sub_cancel]
      _ ≤ ‖z‖ + ‖a - z‖ := norm_add_le _ _
      _ ≤ ‖z‖ + ε := by grw [mem_closedBall_iff_norm.1 az]
  have I : r * ‖(φ' x - A) a‖ ≤ r * (δ + ε) * (‖z‖ + ε) :=
    calc
      r * ‖(φ' x - A) a‖ = ‖(φ' x - A) (r • a)‖ := by
        simp only [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg rpos.le]
      _ = ‖φ y - φ x - A (y - x) - (φ y - φ x - (φ' x) (y - x))‖ := by
        simp only [ya, add_sub_cancel_left, sub_sub_sub_cancel_left, ContinuousLinearMap.coe_sub',
          Pi.sub_apply, map_smul, smul_sub]
      _ ≤ ‖φ y - φ x - A (y - x)‖ + ‖φ y - φ x - (φ' x) (y - x)‖ := norm_sub_le _ _
      _ ≤ δ * ‖y - x‖ + ε * ‖y - x‖ := (add_le_add (hf _ ys _ xs) (hρ ⟨rρ hy, ys⟩))
      _ = r * (δ + ε) * ‖a‖ := by
        simp only [ya, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg rpos.le]
        ring
      _ ≤ r * (δ + ε) * (‖z‖ + ε) := by gcongr
  calc
    ‖(φ' x - A) z‖ = ‖(φ' x - A) a + (φ' x - A) (z - a)‖ := by
      congr 1
      simp only [ContinuousLinearMap.coe_sub', map_sub, Pi.sub_apply]
      abel
    _ ≤ ‖(φ' x - A) a‖ + ‖(φ' x - A) (z - a)‖ := norm_add_le _ _
    _ ≤ (δ + ε) * (‖z‖ + ε) + ‖φ' x - A‖ * ‖z - a‖ := by
      apply add_le_add
      · rw [mul_assoc] at I; exact (mul_le_mul_iff_right₀ rpos).1 I
      · apply ContinuousLinearMap.le_opNorm
    _ ≤ (δ + ε) * (‖z‖ + ε) + ‖φ' x - A‖ * ε := by
      rw [mem_closedBall_iff_norm'] at az
      gcongr

/-! ### The affine graph -/

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

/-! ### Integrand regularity

The area-formula integrand must be continuous (hence measurable, and usable in the
covering/Riemann-sum step): `continuous_jacobian` for the general `√det(DφᵀDφ)`, and
`continuous_graph_integrand` for the graph integrand `√(1 + ‖∇g‖²)`. -/

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

/-! ### The covering step: upper bound for the `C¹` area formula

Combining the per-cell bound (`exists_delta_cell_bound`), the a.e. derivative bound
(`approximatesLinearOn_norm_fderiv_sub_le`), the Jacobian continuity (`continuous_jacobian`)
and Mathlib's `ApproximatesLinearOn` partition, we obtain the area formula's upper inequality
up to an error `2ε·vol A`. This mirrors Mathlib's `addHaar_image_le_lintegral_abs_det_fderiv_aux1`
with `μHE[m]`/`√det(DφᵀDφ)` in place of Haar measure/`|det Dφ|`. -/

set_option linter.unusedSectionVars false in
/-- **Upper bound for the area formula, up to `ε`.** For a `C¹` immersion `φ` on a measurable
set `A` (derivative `φ'` injective on `A`), the `m`-dimensional Euclidean Hausdorff measure of
the image is bounded by the integral of the Jacobian plus an error `2ε·vol A`. -/
theorem μHE_image_le_lintegral_jacobian_aux1 [Nontrivial F]
    {φ : (ℝ^m) → F} {φ' : (ℝ^m) → (ℝ^m) →L[ℝ] F} {A : Set (ℝ^m)} (hA : MeasurableSet A)
    (hφ' : ∀ x ∈ A, HasFDerivWithinAt φ (φ' x) A x)
    (himm : ∀ x ∈ A, Function.Injective (φ' x)) {ε : ℝ≥0} (εpos : 0 < ε) :
    (μHE[m] : Measure F) (φ '' A)
      ≤ (∫⁻ x in A, ENNReal.ofReal (jacobian (φ' x)) ∂volume) + 2 * ε * volume A := by
  -- for each linearization `B`, a tolerance `δ B` with a Jacobian-continuity clause and a
  -- per-cell volume bound (the latter when `B` is injective)
  have key : ∀ B : (ℝ^m) →L[ℝ] F, ∃ δ : ℝ≥0, 0 < δ ∧
      (∀ C : (ℝ^m) →L[ℝ] F, ‖C - B‖ ≤ δ → |jacobian C - jacobian B| ≤ ε) ∧
      (Function.Injective B → ∀ (t : Set (ℝ^m)) (g : (ℝ^m) → F),
        ApproximatesLinearOn g B t δ →
          (μHE[m] : Measure F) (g '' t) ≤ (ENNReal.ofReal (jacobian B) + ε) * volume t) := by
    intro B
    obtain ⟨δ', δ'pos, hδ'⟩ :
        ∃ δ' : ℝ, 0 < δ' ∧ ∀ C, dist C B < δ' → dist (jacobian C) (jacobian B) < ε := by
      refine Metric.continuousAt_iff.1 continuous_jacobian.continuousAt ε ?_
      exact_mod_cast εpos
    set δ'' : ℝ≥0 := ⟨δ' / 2, (half_pos δ'pos).le⟩ with hδ''
    have hcontcl : ∀ C : (ℝ^m) →L[ℝ] F, ‖C - B‖ ≤ δ'' → |jacobian C - jacobian B| ≤ ε := by
      intro C hC
      rw [← Real.dist_eq]
      refine (hδ' C ?_).le
      rw [dist_eq_norm]
      calc ‖C - B‖ ≤ (δ'' : ℝ) := hC
        _ < δ' := by rw [hδ'']; exact half_lt_self δ'pos
    by_cases hBinj : Function.Injective B
    · obtain ⟨δ₁, δ₁pos, hcell⟩ := exists_delta_cell_bound hBinj εpos
      refine ⟨min δ₁ δ'', lt_min δ₁pos (by rw [hδ'']; exact_mod_cast half_pos δ'pos), ?_, ?_⟩
      · intro C hC; exact hcontcl C (hC.trans (by simp))
      · intro _ t g hg; exact hcell t g (hg.mono_num (min_le_left _ _))
    · exact ⟨δ'', by rw [hδ'']; exact_mod_cast half_pos δ'pos, hcontcl, fun h => absurd h hBinj⟩
  choose δ hδ using key
  -- the covering of `A` into cells where `φ` is `δ`-approximated by a constant linear map
  obtain ⟨t, B, t_disj, t_meas, t_cover, ht, hBy⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt φ A φ' hφ' δ fun C => (hδ C).1.ne'
  rcases A.eq_empty_or_nonempty with hAe | hAne
  · simp [hAe]
  · -- every linearization `B n` is injective (it is some `φ' y`, `y ∈ A`)
    have hBinj : ∀ n, Function.Injective (B n) := by
      intro n
      obtain ⟨y, hyA, hy⟩ := hBy hAne n
      rw [hy]; exact himm y hyA
    have Mset : ∀ n : ℕ, MeasurableSet (A ∩ t n) := fun n => hA.inter (t_meas n)
    calc (μHE[m] : Measure F) (φ '' A)
        ≤ (μHE[m] : Measure F) (⋃ n, φ '' (A ∩ t n)) := by
          apply measure_mono
          rw [← image_iUnion, ← inter_iUnion]
          exact image_mono (subset_inter Subset.rfl t_cover)
      _ ≤ ∑' n, (μHE[m] : Measure F) (φ '' (A ∩ t n)) := measure_iUnion_le _
      _ ≤ ∑' n, (ENNReal.ofReal (jacobian (B n)) + ε) * volume (A ∩ t n) := by
          refine ENNReal.tsum_le_tsum fun n => ?_
          exact (hδ (B n)).2.2 (hBinj n) _ _ (ht n)
      _ = ∑' n, ∫⁻ _ in A ∩ t n, (ENNReal.ofReal (jacobian (B n)) + ε) ∂volume := by
          simp only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply, univ_inter]
      _ ≤ ∑' n, ∫⁻ x in A ∩ t n, (ENNReal.ofReal (jacobian (φ' x)) + 2 * ε) ∂volume := by
          refine ENNReal.tsum_le_tsum fun n => ?_
          apply lintegral_mono_ae
          filter_upwards [approximatesLinearOn_norm_fderiv_sub_le (ht n) (Mset n) φ'
            fun x hx => (hφ' x hx.1).mono inter_subset_left] with x hx
          have hJ : |jacobian (φ' x) - jacobian (B n)| ≤ ε :=
            (hδ (B n)).2.1 (φ' x) (by exact_mod_cast hx)
          have hle : jacobian (B n) ≤ jacobian (φ' x) + ε := by
            have := (abs_le.1 hJ).1; linarith
          calc ENNReal.ofReal (jacobian (B n)) + ε
              ≤ ENNReal.ofReal (jacobian (φ' x) + ε) + ε := by gcongr
            _ = ENNReal.ofReal (jacobian (φ' x)) + 2 * ε := by
                rw [ENNReal.ofReal_add (jacobian_nonneg _) (by positivity),
                  ENNReal.ofReal_coe_nnreal]
                ring
      _ = ∫⁻ x in ⋃ n, A ∩ t n, (ENNReal.ofReal (jacobian (φ' x)) + 2 * ε) ∂volume := by
          rw [lintegral_iUnion Mset]
          exact pairwise_disjoint_mono t_disj fun n => inter_subset_right
      _ = ∫⁻ x in A, (ENNReal.ofReal (jacobian (φ' x)) + 2 * ε) ∂volume := by
          rw [← inter_iUnion, inter_eq_self_of_subset_left t_cover]
      _ = (∫⁻ x in A, ENNReal.ofReal (jacobian (φ' x)) ∂volume) + 2 * ε * volume A := by
          simp only [lintegral_add_right' _ aemeasurable_const, setLIntegral_const]

set_option linter.unusedSectionVars false in
/-- Upper bound for finite-measure sets: letting `ε → 0` in the previous lemma. -/
theorem μHE_image_le_lintegral_jacobian_aux2 [Nontrivial F]
    {φ : (ℝ^m) → F} {φ' : (ℝ^m) → (ℝ^m) →L[ℝ] F} {A : Set (ℝ^m)} (hA : MeasurableSet A)
    (h'A : volume A ≠ ∞)
    (hφ' : ∀ x ∈ A, HasFDerivWithinAt φ (φ' x) A x)
    (himm : ∀ x ∈ A, Function.Injective (φ' x)) :
    (μHE[m] : Measure F) (φ '' A) ≤ ∫⁻ x in A, ENNReal.ofReal (jacobian (φ' x)) ∂volume := by
  have htend :
      Tendsto (fun ε : ℝ≥0 => (∫⁻ x in A, ENNReal.ofReal (jacobian (φ' x)) ∂volume)
          + 2 * ε * volume A) (𝓝[>] 0)
        (𝓝 ((∫⁻ x in A, ENNReal.ofReal (jacobian (φ' x)) ∂volume) + 2 * (0 : ℝ≥0) * volume A)) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    refine tendsto_const_nhds.add ?_
    refine ENNReal.Tendsto.mul_const ?_ (Or.inr h'A)
    exact ENNReal.Tendsto.const_mul (ENNReal.tendsto_coe.2 tendsto_id) (Or.inr ENNReal.coe_ne_top)
  simp only [add_zero, zero_mul, mul_zero, ENNReal.coe_zero] at htend
  apply ge_of_tendsto htend
  filter_upwards [self_mem_nhdsWithin] with ε εpos
  rw [mem_Ioi] at εpos
  exact μHE_image_le_lintegral_jacobian_aux1 hA hφ' himm εpos

set_option linter.unusedSectionVars false in
/-- **Upper bound for the `C¹` area formula.** For any measurable set `A` and `C¹` immersion `φ`,
`μHE[m](φ '' A) ≤ ∫_A √det(DφᵀDφ)`. The finite-measure case is extended to all of `A` by covering
with the (disjointed) spanning sets of `volume`. -/
theorem μHE_image_le_lintegral_jacobian [Nontrivial F]
    {φ : (ℝ^m) → F} {φ' : (ℝ^m) → (ℝ^m) →L[ℝ] F} {A : Set (ℝ^m)} (hA : MeasurableSet A)
    (hφ' : ∀ x ∈ A, HasFDerivWithinAt φ (φ' x) A x)
    (himm : ∀ x ∈ A, Function.Injective (φ' x)) :
    (μHE[m] : Measure F) (φ '' A) ≤ ∫⁻ x in A, ENNReal.ofReal (jacobian (φ' x)) ∂volume := by
  set u : ℕ → Set (ℝ^m) := fun n => disjointed (spanningSets (volume : Measure (ℝ^m))) n with hu
  have u_meas : ∀ n, MeasurableSet (u n) :=
    fun n => MeasurableSet.disjointed (fun i => measurableSet_spanningSets _ i) n
  have hcover : A = ⋃ n, A ∩ u n := by
    rw [← inter_iUnion, iUnion_disjointed, iUnion_spanningSets, inter_univ]
  calc (μHE[m] : Measure F) (φ '' A)
      ≤ ∑' n, (μHE[m] : Measure F) (φ '' (A ∩ u n)) := by
        conv_lhs => rw [hcover, image_iUnion]
        exact measure_iUnion_le _
    _ ≤ ∑' n, ∫⁻ x in A ∩ u n, ENNReal.ofReal (jacobian (φ' x)) ∂volume := by
        refine ENNReal.tsum_le_tsum fun n => ?_
        refine μHE_image_le_lintegral_jacobian_aux2 (hA.inter (u_meas n)) ?_
          (fun x hx => (hφ' x hx.1).mono inter_subset_left) (fun x hx => himm x hx.1)
        have hlt : volume (u n) < ∞ :=
          lt_of_le_of_lt (measure_mono (disjointed_subset _ _)) (measure_spanningSets_lt_top _ n)
        exact ne_of_lt (lt_of_le_of_lt (measure_mono inter_subset_right) hlt)
    _ = ∫⁻ x in A, ENNReal.ofReal (jacobian (φ' x)) ∂volume := by
        conv_rhs => rw [hcover]
        rw [lintegral_iUnion (fun n => hA.inter (u_meas n))]
        exact pairwise_disjoint_mono (disjoint_disjointed _) fun n => inter_subset_right

/-! ### The covering step: lower bound for the `C¹` area formula

The reverse inequality `∫_A √det(DφᵀDφ) ≤ μHE[m](φ '' A)`. Here injectivity of `φ` on `A`
(together with continuity, via Lusin–Souslin) is essential: it makes the images of the cells
disjoint, so `measure_image_tsum_of_injOn` turns the covering sum into an exact `μHE[m](φ '' A)`.
This mirrors Mathlib's `lintegral_abs_det_fderiv_le_addHaar_image_aux1`. -/

set_option linter.unusedSectionVars false in
/-- Lower bound up to `ε`: `∫_A √det(DφᵀDφ) ≤ μHE[m](φ '' A) + 2ε·vol A` for a `C¹` immersion `φ`
that is injective on the measurable set `A`. -/
theorem lintegral_jacobian_le_μHE_image_aux1 [Nontrivial F]
    {φ : (ℝ^m) → F} {φ' : (ℝ^m) → (ℝ^m) →L[ℝ] F} {A : Set (ℝ^m)} (hA : MeasurableSet A)
    (hφc : Continuous φ) (hφ' : ∀ x ∈ A, HasFDerivWithinAt φ (φ' x) A x)
    (himm : ∀ x ∈ A, Function.Injective (φ' x)) (hinj : Set.InjOn φ A) {ε : ℝ≥0} (εpos : 0 < ε) :
    (∫⁻ x in A, ENNReal.ofReal (jacobian (φ' x)) ∂volume)
      ≤ (μHE[m] : Measure F) (φ '' A) + 2 * ε * volume A := by
  have key : ∀ B : (ℝ^m) →L[ℝ] F, ∃ δ : ℝ≥0, 0 < δ ∧
      (∀ C : (ℝ^m) →L[ℝ] F, ‖C - B‖ ≤ δ → |jacobian C - jacobian B| ≤ ε) ∧
      (Function.Injective B → ∀ (t : Set (ℝ^m)) (g : (ℝ^m) → F),
        ApproximatesLinearOn g B t δ →
          ENNReal.ofReal (jacobian B) * volume t
            ≤ (μHE[m] : Measure F) (g '' t) + ε * volume t) := by
    intro B
    obtain ⟨δ', δ'pos, hδ'⟩ :
        ∃ δ' : ℝ, 0 < δ' ∧ ∀ C, dist C B < δ' → dist (jacobian C) (jacobian B) < ε := by
      refine Metric.continuousAt_iff.1 continuous_jacobian.continuousAt ε ?_
      exact_mod_cast εpos
    set δ'' : ℝ≥0 := ⟨δ' / 2, (half_pos δ'pos).le⟩ with hδ''
    have hcontcl : ∀ C : (ℝ^m) →L[ℝ] F, ‖C - B‖ ≤ δ'' → |jacobian C - jacobian B| ≤ ε := by
      intro C hC
      rw [← Real.dist_eq]
      refine (hδ' C ?_).le
      rw [dist_eq_norm]
      calc ‖C - B‖ ≤ (δ'' : ℝ) := hC
        _ < δ' := by rw [hδ'']; exact half_lt_self δ'pos
    by_cases hBinj : Function.Injective B
    · obtain ⟨δ₁, δ₁pos, hcell⟩ := exists_delta_cell_bound_lower hBinj εpos
      refine ⟨min δ₁ δ'', lt_min δ₁pos (by rw [hδ'']; exact_mod_cast half_pos δ'pos), ?_, ?_⟩
      · intro C hC; exact hcontcl C (hC.trans (by simp))
      · intro _ t g hg; exact hcell t g (hg.mono_num (min_le_left _ _))
    · exact ⟨δ'', by rw [hδ'']; exact_mod_cast half_pos δ'pos, hcontcl, fun h => absurd h hBinj⟩
  choose δ hδ using key
  obtain ⟨t, B, t_disj, t_meas, t_cover, ht, hBy⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt φ A φ' hφ' δ fun C => (hδ C).1.ne'
  rcases A.eq_empty_or_nonempty with hAe | hAne
  · simp [hAe]
  · have hBinj : ∀ n, Function.Injective (B n) := by
      intro n
      obtain ⟨y, hyA, hy⟩ := hBy hAne n
      rw [hy]; exact himm y hyA
    have Mset : ∀ n : ℕ, MeasurableSet (A ∩ t n) := fun n => hA.inter (t_meas n)
    have s_eq : A = ⋃ n, A ∩ t n := by
      rw [← inter_iUnion]
      exact Subset.antisymm (subset_inter Subset.rfl t_cover) inter_subset_left
    have hvolA : volume A = ∑' n, volume (A ∩ t n) := by
      conv_lhs => rw [s_eq]
      exact measure_iUnion (pairwise_disjoint_mono t_disj fun n => inter_subset_right) Mset
    calc (∫⁻ x in A, ENNReal.ofReal (jacobian (φ' x)) ∂volume)
        = ∑' n, ∫⁻ x in A ∩ t n, ENNReal.ofReal (jacobian (φ' x)) ∂volume := by
          conv_lhs => rw [s_eq]
          rw [lintegral_iUnion Mset
            (pairwise_disjoint_mono t_disj fun n => inter_subset_right)]
      _ ≤ ∑' n, ∫⁻ _ in A ∩ t n, (ENNReal.ofReal (jacobian (B n)) + ε) ∂volume := by
          refine ENNReal.tsum_le_tsum fun n => ?_
          apply lintegral_mono_ae
          filter_upwards [approximatesLinearOn_norm_fderiv_sub_le (ht n) (Mset n) φ'
            fun x hx => (hφ' x hx.1).mono inter_subset_left] with x hx
          have hJ : |jacobian (φ' x) - jacobian (B n)| ≤ ε :=
            (hδ (B n)).2.1 (φ' x) (by exact_mod_cast hx)
          have hle : jacobian (φ' x) ≤ jacobian (B n) + ε := by
            have := (abs_le.1 hJ).2; linarith
          calc ENNReal.ofReal (jacobian (φ' x))
              ≤ ENNReal.ofReal (jacobian (B n) + ε) := ENNReal.ofReal_le_ofReal hle
            _ = ENNReal.ofReal (jacobian (B n)) + ε := by
                rw [ENNReal.ofReal_add (jacobian_nonneg _) (by positivity),
                  ENNReal.ofReal_coe_nnreal]
      _ = ∑' n, (ENNReal.ofReal (jacobian (B n)) * volume (A ∩ t n) + ε * volume (A ∩ t n)) := by
          simp only [setLIntegral_const, lintegral_add_right _ measurable_const]
      _ ≤ ∑' n, ((μHE[m] : Measure F) (φ '' (A ∩ t n)) + ε * volume (A ∩ t n)
            + ε * volume (A ∩ t n)) := by
          gcongr with n
          exact (hδ (B n)).2.2 (hBinj n) _ _ (ht n)
      _ = (μHE[m] : Measure F) (φ '' A) + 2 * ε * volume A := by
          rw [measure_image_tsum_of_injOn hφc hA hinj t_disj t_meas t_cover, hvolA,
            ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
          congr 1
          ext1 n
          rw [mul_assoc, two_mul, add_assoc]

set_option linter.unusedSectionVars false in
/-- Lower bound for finite-measure sets: letting `ε → 0` in the previous lemma. -/
theorem lintegral_jacobian_le_μHE_image_aux2 [Nontrivial F]
    {φ : (ℝ^m) → F} {φ' : (ℝ^m) → (ℝ^m) →L[ℝ] F} {A : Set (ℝ^m)} (hA : MeasurableSet A)
    (h'A : volume A ≠ ∞) (hφc : Continuous φ)
    (hφ' : ∀ x ∈ A, HasFDerivWithinAt φ (φ' x) A x)
    (himm : ∀ x ∈ A, Function.Injective (φ' x)) (hinj : Set.InjOn φ A) :
    (∫⁻ x in A, ENNReal.ofReal (jacobian (φ' x)) ∂volume) ≤ (μHE[m] : Measure F) (φ '' A) := by
  have htend :
      Tendsto (fun ε : ℝ≥0 => (μHE[m] : Measure F) (φ '' A) + 2 * ε * volume A) (𝓝[>] 0)
        (𝓝 ((μHE[m] : Measure F) (φ '' A) + 2 * (0 : ℝ≥0) * volume A)) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    refine tendsto_const_nhds.add ?_
    refine ENNReal.Tendsto.mul_const ?_ (Or.inr h'A)
    exact ENNReal.Tendsto.const_mul (ENNReal.tendsto_coe.2 tendsto_id) (Or.inr ENNReal.coe_ne_top)
  simp only [add_zero, zero_mul, mul_zero, ENNReal.coe_zero] at htend
  apply ge_of_tendsto htend
  filter_upwards [self_mem_nhdsWithin] with ε εpos
  rw [mem_Ioi] at εpos
  exact lintegral_jacobian_le_μHE_image_aux1 hA hφc hφ' himm hinj εpos

set_option linter.unusedSectionVars false in
/-- **Lower bound for the `C¹` area formula.** For any measurable set `A` and `C¹` immersion `φ`
that is injective on `A`, `∫_A √det(DφᵀDφ) ≤ μHE[m](φ '' A)`. -/
theorem lintegral_jacobian_le_μHE_image [Nontrivial F]
    {φ : (ℝ^m) → F} {φ' : (ℝ^m) → (ℝ^m) →L[ℝ] F} {A : Set (ℝ^m)} (hA : MeasurableSet A)
    (hφc : Continuous φ) (hφ' : ∀ x ∈ A, HasFDerivWithinAt φ (φ' x) A x)
    (himm : ∀ x ∈ A, Function.Injective (φ' x)) (hinj : Set.InjOn φ A) :
    (∫⁻ x in A, ENNReal.ofReal (jacobian (φ' x)) ∂volume) ≤ (μHE[m] : Measure F) (φ '' A) := by
  set u : ℕ → Set (ℝ^m) := fun n => disjointed (spanningSets (volume : Measure (ℝ^m))) n with hu
  have u_meas : ∀ n, MeasurableSet (u n) :=
    fun n => MeasurableSet.disjointed (fun i => measurableSet_spanningSets _ i) n
  have u_disj : Pairwise (Function.onFun Disjoint u) := disjoint_disjointed _
  have hcover : A = ⋃ n, A ∩ u n := by
    rw [← inter_iUnion, iUnion_disjointed, iUnion_spanningSets, inter_univ]
  have hAcov : A ⊆ ⋃ n, u n := by
    rw [hcover]; exact iUnion_mono fun n => inter_subset_right
  calc (∫⁻ x in A, ENNReal.ofReal (jacobian (φ' x)) ∂volume)
      = ∑' n, ∫⁻ x in A ∩ u n, ENNReal.ofReal (jacobian (φ' x)) ∂volume := by
        conv_lhs => rw [hcover]
        rw [lintegral_iUnion (fun n => hA.inter (u_meas n))
          (pairwise_disjoint_mono u_disj fun n => inter_subset_right)]
    _ ≤ ∑' n, (μHE[m] : Measure F) (φ '' (A ∩ u n)) := by
        refine ENNReal.tsum_le_tsum fun n => ?_
        refine lintegral_jacobian_le_μHE_image_aux2 (hA.inter (u_meas n)) ?_ hφc
          (fun x hx => (hφ' x hx.1).mono inter_subset_left) (fun x hx => himm x hx.1)
          (hinj.mono inter_subset_left)
        have hlt : volume (u n) < ∞ :=
          lt_of_le_of_lt (measure_mono (disjointed_subset _ _)) (measure_spanningSets_lt_top _ n)
        exact ne_of_lt (lt_of_le_of_lt (measure_mono inter_subset_right) hlt)
    _ = (μHE[m] : Measure F) (φ '' A) :=
        (measure_image_tsum_of_injOn hφc hA hinj u_disj u_meas hAcov).symm

/-- **The `C¹` area formula.** For a `C¹` immersion `φ : ℝᵐ → F` (derivative `φ'` injective at
every point of `A`) that is injective on a measurable set `A`,
`μHE[m](φ '' A) = ∫_A √det(Dφ(x)ᵀ Dφ(x))`. The `m`-dimensional Euclidean Hausdorff measure of the
image equals the integral of the Jacobian over `A`. -/
theorem area_formula [Nontrivial F]
    {φ : (ℝ^m) → F} {φ' : (ℝ^m) → (ℝ^m) →L[ℝ] F} {A : Set (ℝ^m)} (hA : MeasurableSet A)
    (hφc : Continuous φ) (hφ' : ∀ x ∈ A, HasFDerivWithinAt φ (φ' x) A x)
    (himm : ∀ x ∈ A, Function.Injective (φ' x)) (hinj : Set.InjOn φ A) :
    (μHE[m] : Measure F) (φ '' A) = ∫⁻ x in A, ENNReal.ofReal (jacobian (φ' x)) ∂volume :=
  le_antisymm (μHE_image_le_lintegral_jacobian hA hφ' himm)
    (lintegral_jacobian_le_μHE_image hA hφc hφ' himm hinj)

/-! ### Integral (change-of-variables) form

The area formula upgrades from a measure identity to a change-of-variables formula for integrals:
the pushforward of `√det(DφᵀDφ)·volume` along `φ` is `μHE[m]` on the image, hence
`∫_{φ''A} f dμHE = ∫_A f(φ x)·√det(DφᵀDφ) dx`. This is the form consumed by surface integrals. -/

set_option linter.unusedSectionVars false in
/-- Pushforward form of the area formula: the image measure under `φ` of the density
`√det(DφᵀDφ)·volume` on `A` is the Euclidean Hausdorff measure restricted to `φ '' A`. -/
theorem map_withDensity_jacobian [Nontrivial F]
    {φ : (ℝ^m) → F} {φ' : (ℝ^m) → (ℝ^m) →L[ℝ] F} {A : Set (ℝ^m)} (hA : MeasurableSet A)
    (hφc : Continuous φ) (hφ' : ∀ x ∈ A, HasFDerivWithinAt φ (φ' x) A x)
    (himm : ∀ x ∈ A, Function.Injective (φ' x)) (hinj : Set.InjOn φ A) :
    Measure.map φ ((volume.restrict A).withDensity (fun x => ENNReal.ofReal (jacobian (φ' x))))
      = (μHE[m] : Measure F).restrict (φ '' A) := by
  have hφm : Measurable φ := hφc.measurable
  refine Measure.ext fun t ht => ?_
  have hpre : MeasurableSet (φ ⁻¹' t) := hφm ht
  rw [Measure.map_apply hφm ht, withDensity_apply _ hpre,
    Measure.restrict_restrict hpre, Measure.restrict_apply ht,
    Set.inter_comm (φ ⁻¹' t) A, Set.inter_comm t (φ '' A), ← Set.image_inter_preimage]
  exact (area_formula (hA.inter hpre) hφc
    (fun x hx => (hφ' x hx.1).mono inter_subset_left) (fun x hx => himm x hx.1)
    (hinj.mono inter_subset_left)).symm

set_option linter.unusedSectionVars false in
/-- **Integral form of the area formula.** For a `C¹` immersion `φ` injective on a measurable set
`A`, with measurable derivative `φ'`, and a measurable `f : F → ℝ≥0∞`,
`∫_{φ''A} f dμHE = ∫_A f(φ x)·√det(DφᵀDφ) dx`. -/
theorem lintegral_image_jacobian_mul [Nontrivial F]
    {φ : (ℝ^m) → F} {φ' : (ℝ^m) → (ℝ^m) →L[ℝ] F} {A : Set (ℝ^m)} (hA : MeasurableSet A)
    (hφc : Continuous φ) (hφ' : ∀ x ∈ A, HasFDerivWithinAt φ (φ' x) A x)
    (himm : ∀ x ∈ A, Function.Injective (φ' x)) (hinj : Set.InjOn φ A)
    (hφ'm : AEMeasurable φ' (volume.restrict A)) {f : F → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y in φ '' A, f y ∂(μHE[m] : Measure F)
      = ∫⁻ x in A, f (φ x) * ENNReal.ofReal (jacobian (φ' x)) ∂volume := by
  have hφm : Measurable φ := hφc.measurable
  have hD : AEMeasurable (fun x => ENNReal.ofReal (jacobian (φ' x))) (volume.restrict A) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (continuous_jacobian.measurable.comp_aemeasurable hφ'm)
  rw [← map_withDensity_jacobian hA hφc hφ' himm hinj, lintegral_map hf hφm,
    lintegral_withDensity_eq_lintegral_mul₀ (g := fun a => f (φ a)) hD
      (hf.comp hφm).aemeasurable]
  simp only [Pi.mul_apply]
  refine lintegral_congr fun x => ?_
  rw [mul_comm]

set_option linter.unusedSectionVars false in
/-- **Bochner change-of-variables form of the area formula.** For a `C¹` immersion `φ` injective on
a measurable set `A`, with measurable derivative `φ'`, and a vector-valued `g : F → E` strongly
measurable on `φ''A`, `∫_{φ''A} g dμHE = ∫_A √det(DφᵀDφ) • g(φ x) dx`. This is the signed /
vector-valued form needed for flux integrals and the divergence theorem. -/
theorem setIntegral_image_jacobian_smul [Nontrivial F]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : (ℝ^m) → F} {φ' : (ℝ^m) → (ℝ^m) →L[ℝ] F} {A : Set (ℝ^m)} (hA : MeasurableSet A)
    (hφc : Continuous φ) (hφ' : ∀ x ∈ A, HasFDerivWithinAt φ (φ' x) A x)
    (himm : ∀ x ∈ A, Function.Injective (φ' x)) (hinj : Set.InjOn φ A)
    (hφ'm : AEMeasurable φ' (volume.restrict A)) {g : F → E}
    (hg : AEStronglyMeasurable g ((μHE[m] : Measure F).restrict (φ '' A))) :
    ∫ y in φ '' A, g y ∂(μHE[m] : Measure F)
      = ∫ x in A, jacobian (φ' x) • g (φ x) ∂volume := by
  have hmap := map_withDensity_jacobian hA hφc hφ' himm hinj
  have hToNNReal : AEMeasurable (fun x => (jacobian (φ' x)).toNNReal) (volume.restrict A) :=
    measurable_real_toNNReal.comp_aemeasurable
      (continuous_jacobian.measurable.comp_aemeasurable hφ'm)
  have hg' : AEStronglyMeasurable g (Measure.map φ
      ((volume.restrict A).withDensity fun x => ENNReal.ofReal (jacobian (φ' x)))) := by
    rw [hmap]; exact hg
  rw [← hmap, integral_map hφc.measurable.aemeasurable hg']
  simp only [ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul₀ hToNNReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [NNReal.smul_def, Real.coe_toNNReal _ (jacobian_nonneg (φ' x))]

/-! ### The `C¹` graph: the concrete surface-area formula

Specializing `area_formula` to the graph map `Φ y = (y, g y)` of a `C¹` function `g : ℝᵐ → ℝ`
yields `μHE[m](Φ '' A) = ∫_A √(1 + ‖∇g‖²)`. The graph map is globally injective (its first
coordinate is the identity) and its derivative is the affine graph map `graphMap (∇g x)`, whose
Gram determinant is `1 + ‖∇g x‖²` (`graph_gram_det`). -/

/-- The `C¹` graph map `y ↦ (y, g y)` into the `L²` product `WithLp 2 (ℝᵐ × ℝ)`. -/
def graphFun (g : (ℝ^m) → ℝ) (y : ℝ^m) : WithLp 2 ((ℝ^m) × ℝ) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ (ℝ^m) ℝ).symm (y, g y)

/-- The derivative of the graph map at `x`, packaged as a continuous linear map. -/
def graphFun' (g : (ℝ^m) → ℝ) (x : ℝ^m) : (ℝ^m) →L[ℝ] WithLp 2 ((ℝ^m) × ℝ) :=
  ((WithLp.prodContinuousLinearEquiv 2 ℝ (ℝ^m) ℝ).symm :
      ((ℝ^m) × ℝ) →L[ℝ] WithLp 2 ((ℝ^m) × ℝ)).comp
    ((ContinuousLinearMap.id ℝ (ℝ^m)).prod (fderiv ℝ g x))

theorem hasFDerivAt_graphFun {g : (ℝ^m) → ℝ} (hg : ContDiff ℝ 1 g) (x : ℝ^m) :
    HasFDerivAt (graphFun g) (graphFun' g x) x := by
  have hgd : HasFDerivAt g (fderiv ℝ g x) x := (hg.differentiable (by norm_num) x).hasFDerivAt
  have hprod : HasFDerivAt (fun y => (y, g y))
      ((ContinuousLinearMap.id ℝ (ℝ^m)).prod (fderiv ℝ g x)) x :=
    (hasFDerivAt_id x).prodMk hgd
  exact (((WithLp.prodContinuousLinearEquiv 2 ℝ (ℝ^m) ℝ).symm :
    ((ℝ^m) × ℝ) →L[ℝ] WithLp 2 ((ℝ^m) × ℝ)).hasFDerivAt).comp x hprod

theorem graphFun'_toLinearMap {g : (ℝ^m) → ℝ} (hg : ContDiff ℝ 1 g) (x : ℝ^m) :
    (graphFun' g x).toLinearMap = graphMap (gradient g x) := by
  ext v
  change (WithLp.prodContinuousLinearEquiv 2 ℝ (ℝ^m) ℝ).symm (v, fderiv ℝ g x v)
    = graphMap (gradient g x) v
  rw [← inner_gradient_left (hg.differentiable (by norm_num) x)]
  rfl

theorem jacobian_graphFun' {g : (ℝ^m) → ℝ} (hg : ContDiff ℝ 1 g) (x : ℝ^m) :
    jacobian (graphFun' g x) = Real.sqrt (1 + ‖gradient g x‖ ^ 2) := by
  rw [jacobian, graphFun'_toLinearMap hg, graph_gram_det]

theorem injective_graphFun (g : (ℝ^m) → ℝ) : Function.Injective (graphFun g) := by
  intro a b h
  have := (WithLp.prodContinuousLinearEquiv 2 ℝ (ℝ^m) ℝ).symm.injective h
  exact (Prod.ext_iff.1 this).1

theorem continuous_graphFun {g : (ℝ^m) → ℝ} (hg : Continuous g) : Continuous (graphFun g) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ (ℝ^m) ℝ).symm.continuous.comp
    (continuous_id.prodMk hg)

/-- **The `C¹` graph area formula.** The `m`-dimensional Euclidean Hausdorff measure of the graph
of a `C¹` function `g : ℝᵐ → ℝ` over a measurable set `A` equals `∫_A √(1 + ‖∇g‖²)`. This is the
concrete surface-area theorem for a `C¹` graph — the form used for boundary integrals. -/
theorem area_formula_graph {g : (ℝ^m) → ℝ} (hg : ContDiff ℝ 1 g) {A : Set (ℝ^m)}
    (hA : MeasurableSet A) :
    (μHE[m] : Measure (WithLp 2 ((ℝ^m) × ℝ))) (graphFun g '' A)
      = ∫⁻ x in A, ENNReal.ofReal (Real.sqrt (1 + ‖gradient g x‖ ^ 2)) ∂volume := by
  have hinj' : ∀ x, Function.Injective (graphFun' g x) := by
    intro x a b h
    have hcoe : (graphFun' g x : (ℝ^m) → _) = graphMap (gradient g x) := by
      funext v; exact LinearMap.congr_fun (graphFun'_toLinearMap hg x) v
    exact graph_injective (gradient g x) (by simpa only [hcoe] using h)
  rw [area_formula hA (continuous_graphFun hg.continuous)
    (fun x _ => (hasFDerivAt_graphFun hg x).hasFDerivWithinAt)
    (fun x _ => hinj' x) (injective_graphFun g).injOn]
  exact lintegral_congr fun x => by rw [jacobian_graphFun' hg]

theorem contDiff_graphFun {g : (ℝ^m) → ℝ} (hg : ContDiff ℝ 1 g) : ContDiff ℝ 1 (graphFun g) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ (ℝ^m) ℝ).symm.contDiff.comp (contDiff_id.prodMk hg)

theorem continuous_graphFun' {g : (ℝ^m) → ℝ} (hg : ContDiff ℝ 1 g) :
    Continuous (graphFun' g) := by
  have heq : graphFun' g = fderiv ℝ (graphFun g) :=
    funext fun x => ((hasFDerivAt_graphFun hg x).fderiv).symm
  rw [heq]
  exact (contDiff_graphFun hg).continuous_fderiv (by norm_num)

theorem injective_graphFun' {g : (ℝ^m) → ℝ} (hg : ContDiff ℝ 1 g) (x : ℝ^m) :
    Function.Injective (graphFun' g x) := by
  have hcoe : (graphFun' g x : (ℝ^m) → _) = graphMap (gradient g x) := by
    funext v; exact LinearMap.congr_fun (graphFun'_toLinearMap hg x) v
  exact fun a b h => graph_injective (gradient g x) (by simpa only [hcoe] using h)

set_option linter.style.longLine false in
/-- **Integral form of the `C¹` graph area formula.** `∫_{graph g '' A} f dμHE =
∫_A f(x, g x)·√(1 + ‖∇g x‖²) dx` for measurable `f`. The concrete surface-integral
change-of-variables for a `C¹` graph. -/
theorem lintegral_image_graph_mul {g : (ℝ^m) → ℝ} (hg : ContDiff ℝ 1 g) {A : Set (ℝ^m)}
    (hA : MeasurableSet A) {f : WithLp 2 ((ℝ^m) × ℝ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y in graphFun g '' A, f y ∂(μHE[m] : Measure (WithLp 2 ((ℝ^m) × ℝ)))
      = ∫⁻ x in A, f (graphFun g x) * ENNReal.ofReal (Real.sqrt (1 + ‖gradient g x‖ ^ 2)) ∂volume := by
  rw [lintegral_image_jacobian_mul hA (continuous_graphFun hg.continuous)
    (fun x _ => (hasFDerivAt_graphFun hg x).hasFDerivWithinAt) (fun x _ => injective_graphFun' hg x)
    (injective_graphFun g).injOn (continuous_graphFun' hg).aemeasurable hf]
  refine lintegral_congr fun x => ?_
  rw [jacobian_graphFun' hg]

set_option linter.unusedSectionVars false in
/-- **Bochner change-of-variables for the `C¹` graph.** For `γ : ℝᵐ → ℝ` of class `C¹` and `f`
strongly measurable on the graph, `∫_{graph γ '' A} f dμHE = ∫_A √(1+‖∇γ‖²) • f(x, γ x) dx`. -/
theorem setIntegral_image_graph_smul {γ : (ℝ^m) → ℝ} (hγ : ContDiff ℝ 1 γ) {A : Set (ℝ^m)}
    (hA : MeasurableSet A) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : WithLp 2 ((ℝ^m) × ℝ) → E}
    (hf : AEStronglyMeasurable f ((μHE[m] : Measure (WithLp 2 ((ℝ^m) × ℝ))).restrict
      (graphFun γ '' A))) :
    ∫ y in graphFun γ '' A, f y ∂(μHE[m] : Measure (WithLp 2 ((ℝ^m) × ℝ)))
      = ∫ x in A, Real.sqrt (1 + ‖gradient γ x‖ ^ 2) • f (graphFun γ x) ∂volume := by
  rw [setIntegral_image_jacobian_smul hA (continuous_graphFun hγ.continuous)
    (fun x _ => (hasFDerivAt_graphFun hγ x).hasFDerivWithinAt) (fun x _ => injective_graphFun' hγ x)
    (injective_graphFun γ).injOn (continuous_graphFun' hγ).aemeasurable hf]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [jacobian_graphFun' hγ]

/-! ### The divergence theorem: the graph flux identity

The first Gauss–Green building block: the flux of a vector field through a `C¹` graph, with the
area-element square root cancelled against the unit normal's denominator. -/

/-- The upward unit normal to the graph of `γ` over the base point `x`, as an element of
`WithLp 2 (ℝᵐ × ℝ)`: `ν(x) = (−∇γ x, 1)/√(1 + ‖∇γ x‖²)`. -/
def graphNormal (γ : (ℝ^m) → ℝ) (x : ℝ^m) : WithLp 2 ((ℝ^m) × ℝ) :=
  (Real.sqrt (1 + ‖gradient γ x‖ ^ 2))⁻¹ • WithLp.toLp 2 (-gradient γ x, (1 : ℝ))

/-- The upward graph normal `graphNormal γ x` is a **unit** vector — it is genuinely the unit normal
to the graph, the local model for the outward normal of a bounded `C¹` domain. -/
theorem norm_graphNormal (γ : (ℝ^m) → ℝ) (x : ℝ^m) : ‖graphNormal γ x‖ = 1 := by
  have hpos : (0:ℝ) < Real.sqrt (1 + ‖gradient γ x‖ ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hnorm : ‖WithLp.toLp 2 ((-gradient γ x : ℝ^m), (1:ℝ))‖
      = Real.sqrt (1 + ‖gradient γ x‖ ^ 2) := by
    rw [WithLp.prod_norm_eq_of_L2]
    congr 1
    change ‖(-gradient γ x : ℝ^m)‖ ^ 2 + ‖(1:ℝ)‖ ^ 2 = 1 + ‖gradient γ x‖ ^ 2
    rw [norm_neg, norm_one]; ring
  rw [graphNormal, norm_smul, hnorm, Real.norm_eq_abs, abs_inv, abs_of_pos hpos,
    inv_mul_cancel₀ hpos.ne']

/-- The upward unit normal of a `C¹` graph depends continuously on the base point. -/
theorem continuous_graphNormal {γ : (ℝ^m) → ℝ} (hγ : ContDiff ℝ 1 γ) :
    Continuous (graphNormal γ) := by
  unfold graphNormal
  refine Continuous.smul ?_ ?_
  · exact (continuous_graph_integrand hγ).inv₀
      (fun x => (Real.sqrt_pos.mpr (by positivity)).ne')
  · exact (WithLp.prodContinuousLinearEquiv 2 ℝ (ℝ^m) ℝ).symm.continuous.comp
      ((continuous_gradient hγ).neg.prodMk continuous_const)

set_option linter.unusedSectionVars false in
/-- **Graph flux identity (Gauss–Green building block).** The flux of a vector field `V` through
the graph of a `C¹` function `γ` equals a base integral with the area-element square root
cancelled: `∫_{graph} ⟪V, ν⟫ dμHE = ∫_A (V₂(x,γx) − ⟪V₁(x,γx), ∇γ x⟫) dx`, where `ν` is the
upward unit normal and `V = (V₁, V₂)`. -/
theorem flux_graph {γ : (ℝ^m) → ℝ} (hγ : ContDiff ℝ 1 γ) {A : Set (ℝ^m)} (hA : MeasurableSet A)
    {V : WithLp 2 ((ℝ^m) × ℝ) → WithLp 2 ((ℝ^m) × ℝ)}
    (hV : AEStronglyMeasurable (fun y => ⟪V y, graphNormal γ y.ofLp.1⟫)
      ((μHE[m] : Measure (WithLp 2 ((ℝ^m) × ℝ))).restrict (graphFun γ '' A))) :
    ∫ y in graphFun γ '' A, (⟪V y, graphNormal γ y.ofLp.1⟫ : ℝ)
        ∂(μHE[m] : Measure (WithLp 2 ((ℝ^m) × ℝ)))
      = ∫ x in A, ((V (graphFun γ x)).ofLp.2
          - ⟪(V (graphFun γ x)).ofLp.1, gradient γ x⟫) ∂volume := by
  rw [setIntegral_image_graph_smul hγ hA hV]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  rw [show (graphFun γ x).ofLp.1 = x from rfl, graphNormal]
  set s : ℝ := Real.sqrt (1 + ‖gradient γ x‖ ^ 2) with hs
  have hspos : 0 < s := Real.sqrt_pos.mpr (by positivity)
  rw [real_inner_smul_right, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hspos.ne', one_mul,
    WithLp.prod_inner_apply]
  simp only [inner_neg_right]
  have hone : (⟪(V (graphFun γ x)).ofLp.2, (1 : ℝ)⟫ : ℝ) = (V (graphFun γ x)).ofLp.2 := by
    have h2 : (⟪(V (graphFun γ x)).ofLp.2, (1 : ℝ)⟫ : ℝ)
        = ⟪(V (graphFun γ x)).ofLp.2 • (1 : ℝ), (1 : ℝ)⟫ := by rw [smul_eq_mul, mul_one]
    rw [h2, real_inner_smul_left, real_inner_self_eq_norm_sq, norm_one]; ring
  rw [hone]; ring

set_option linter.unusedSectionVars false in
/-- **Vertical flux through a graph.** The flux of the purely vertical field `y ↦ (0, f y)` through
the graph of `γ` is the integral of its top values: `∫_{graph} ⟪(0,f), ν⟫ dμHE = ∫_A f(x, γx) dx`
(the `∇γ` term drops out). This is the top-boundary term of the divergence theorem. -/
theorem flux_graph_vertical {γ : (ℝ^m) → ℝ} (hγ : ContDiff ℝ 1 γ) {A : Set (ℝ^m)}
    (hA : MeasurableSet A) {f : WithLp 2 ((ℝ^m) × ℝ) → ℝ}
    (hf : AEStronglyMeasurable
      (fun y => ⟪WithLp.toLp 2 ((0 : ℝ^m), f y), graphNormal γ y.ofLp.1⟫)
      ((μHE[m] : Measure (WithLp 2 ((ℝ^m) × ℝ))).restrict (graphFun γ '' A))) :
    ∫ y in graphFun γ '' A, (⟪WithLp.toLp 2 ((0 : ℝ^m), f y), graphNormal γ y.ofLp.1⟫ : ℝ)
        ∂(μHE[m] : Measure (WithLp 2 ((ℝ^m) × ℝ)))
      = ∫ x in A, f (graphFun γ x) ∂volume := by
  rw [flux_graph hγ hA hf]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [inner_zero_left]

set_option linter.unusedSectionVars false in
/-- FTC over the fibres of a subgraph: `∫_A (∫₀^{γx} ∂ₜF) dx = ∫_A (F(x,γx) − F(x,0)) dx`, the
volume side of the divergence theorem written as an iterated integral. -/
theorem ftc_subgraph {γ : (ℝ^m) → ℝ} {F : (ℝ^m) → ℝ → ℝ} (hF : ∀ x, ContDiff ℝ 1 (F x))
    {A : Set (ℝ^m)} :
    ∫ x in A, (∫ t in (0 : ℝ)..(γ x), deriv (F x) t) ∂volume
      = ∫ x in A, (F x (γ x) - F x 0) ∂volume := by
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  refine intervalIntegral.integral_deriv_eq_sub (fun t _ => ?_) ?_
  · exact (hF x).differentiable (by norm_num) t
  · exact ((hF x).continuous_deriv (by norm_num)).intervalIntegrable _ _

set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- **Divergence theorem over a subgraph (iterated form).** For `F : ℝᵐ → ℝ → ℝ` with each `F x`
of class `C¹`, the volume integral of `∂ₜF` over the region under the graph of `γ` (written as an
iterated integral) equals the top-boundary flux minus the bottom integral:
`∫_A (∫₀^{γx} ∂ₜF) dx = ∫_{graph} ⟪(0,F), ν⟫ dμHE − ∫_A F(x,0) dx`. -/
theorem divergence_subgraph {γ : (ℝ^m) → ℝ} (hγ : ContDiff ℝ 1 γ) {A : Set (ℝ^m)}
    (hA : MeasurableSet A) {F : (ℝ^m) → ℝ → ℝ} (hF : ∀ x, ContDiff ℝ 1 (F x))
    (hmeas : AEStronglyMeasurable
      (fun y => ⟪WithLp.toLp 2 ((0 : ℝ^m), F y.ofLp.1 y.ofLp.2), graphNormal γ y.ofLp.1⟫)
      ((μHE[m] : Measure (WithLp 2 ((ℝ^m) × ℝ))).restrict (graphFun γ '' A)))
    (hint0 : IntegrableOn (fun x => F x 0) A) (hintγ : IntegrableOn (fun x => F x (γ x)) A) :
    ∫ x in A, (∫ t in (0 : ℝ)..(γ x), deriv (F x) t) ∂volume
      = (∫ y in graphFun γ '' A,
            (⟪WithLp.toLp 2 ((0 : ℝ^m), F y.ofLp.1 y.ofLp.2), graphNormal γ y.ofLp.1⟫ : ℝ)
            ∂(μHE[m] : Measure (WithLp 2 ((ℝ^m) × ℝ))))
          - ∫ x in A, F x 0 ∂volume := by
  rw [ftc_subgraph hF, flux_graph_vertical hγ hA hmeas, integral_sub hintγ hint0]
  congr 1

/-! ### Geometric form via Fubini

Upgrading the iterated integral to a genuine volume integral over the region `Ω` under the graph,
using `WithLp.volume_preserving_ofLp` (implicitly, via `volume_eq_prod` on `ℝᵐ × ℝ`) and Fubini. -/

set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Fubini over the region under a graph: the integral of `h` over `regionBetween 0 γ A` equals
the iterated integral `∫_A ∫_{Ioo 0 (γx)} h(x,t) dt dx`. -/
theorem setIntegral_regionBetween {γ : (ℝ^m) → ℝ} (hγ : Measurable γ) {A : Set (ℝ^m)}
    (hA : MeasurableSet A) {h : (ℝ^m) × ℝ → ℝ}
    (hint : IntegrableOn h (regionBetween (fun _ => (0 : ℝ)) γ A)) :
    ∫ p in regionBetween (fun _ => (0 : ℝ)) γ A, h p ∂(volume : Measure ((ℝ^m) × ℝ))
      = ∫ x in A, (∫ t in Set.Ioo 0 (γ x), h (x, t)) ∂volume := by
  have hmS : MeasurableSet (regionBetween (fun _ => (0 : ℝ)) γ A) :=
    measurableSet_regionBetween measurable_const hγ hA
  have hint' : Integrable
      (fun p => (regionBetween (fun _ => (0 : ℝ)) γ A).indicator h p) (volume : Measure ((ℝ^m) × ℝ)) :=
    (integrable_indicator_iff hmS).mpr hint
  rw [← integral_indicator hmS, volume_eq_prod,
    integral_prod _ (by rw [← volume_eq_prod]; exact hint')]
  have hslice : (fun x => ∫ t, (regionBetween (fun _ => (0 : ℝ)) γ A).indicator h (x, t) ∂volume)
      = A.indicator (fun x => ∫ t in Set.Ioo (0 : ℝ) (γ x), h (x, t)) := by
    funext x
    by_cases hxA : x ∈ A
    · rw [Set.indicator_of_mem hxA]
      have hfun : (fun t => (regionBetween (fun _ => (0 : ℝ)) γ A).indicator h (x, t))
          = (Set.Ioo (0 : ℝ) (γ x)).indicator (fun t => h (x, t)) := by
        funext t
        by_cases htI : t ∈ Set.Ioo (0 : ℝ) (γ x)
        · rw [Set.indicator_of_mem htI, Set.indicator_of_mem (show
            (x, t) ∈ regionBetween (fun _ => (0 : ℝ)) γ A from ⟨hxA, htI⟩)]
        · rw [Set.indicator_of_notMem htI, Set.indicator_of_notMem (fun hmem => htI hmem.2)]
      rw [hfun, integral_indicator measurableSet_Ioo]
    · rw [Set.indicator_of_notMem hxA]
      have hfun : (fun t => (regionBetween (fun _ => (0 : ℝ)) γ A).indicator h (x, t))
          = fun _ => 0 := by
        funext t; exact Set.indicator_of_notMem (fun hmem => hxA hmem.1) _
      rw [hfun, integral_zero]
  rw [hslice, integral_indicator hA]

set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- **Divergence theorem over a subgraph (geometric form).** For `γ ≥ 0` of class `C¹` and each
`F x` of class `C¹`, the genuine volume integral of `∂ₜF` over the region `Ω = {(x,t): x∈A,
0<t<γx}` equals the top-boundary flux minus the bottom integral. -/
theorem divergence_subgraph_geometric {γ : (ℝ^m) → ℝ} (hγ : ContDiff ℝ 1 γ) (hγ0 : ∀ x, 0 ≤ γ x)
    {A : Set (ℝ^m)} (hA : MeasurableSet A) {F : (ℝ^m) → ℝ → ℝ} (hF : ∀ x, ContDiff ℝ 1 (F x))
    (hmeas : AEStronglyMeasurable
      (fun y => ⟪WithLp.toLp 2 ((0 : ℝ^m), F y.ofLp.1 y.ofLp.2), graphNormal γ y.ofLp.1⟫)
      ((μHE[m] : Measure (WithLp 2 ((ℝ^m) × ℝ))).restrict (graphFun γ '' A)))
    (hint0 : IntegrableOn (fun x => F x 0) A) (hintγ : IntegrableOn (fun x => F x (γ x)) A)
    (hregint : IntegrableOn (fun p => deriv (F p.1) p.2)
      (regionBetween (fun _ => (0 : ℝ)) γ A)) :
    ∫ p in regionBetween (fun _ => (0 : ℝ)) γ A, deriv (F p.1) p.2
        ∂(volume : Measure ((ℝ^m) × ℝ))
      = (∫ y in graphFun γ '' A,
            (⟪WithLp.toLp 2 ((0 : ℝ^m), F y.ofLp.1 y.ofLp.2), graphNormal γ y.ofLp.1⟫ : ℝ)
            ∂(μHE[m] : Measure (WithLp 2 ((ℝ^m) × ℝ))))
          - ∫ x in A, F x 0 ∂volume := by
  rw [setIntegral_regionBetween hγ.continuous.measurable hA hregint,
    ← divergence_subgraph hγ hA hF hmeas hint0 hintγ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  rw [intervalIntegral.integral_of_le (hγ0 x), integral_Ioc_eq_integral_Ioo]

/-! ### The full-gradient divergence theorem (Gauss–Green)

The capstone: the genuine divergence theorem `∫_Ω div F = ∫_∂Ω ⟪F, ν⟫` for a `C¹` vector field
over the region under a `C¹` graph. The horizontal half (`horizontal_sum`) is the coordinate sum
of `Calculus.integral_horizontal_ibp_euclidean`; the vertical half (`vertical_ftc`) is the
fibrewise fundamental theorem of calculus; the two are reconciled with the surface flux via
`flux_graph`. -/

set_option linter.style.longLine false in
/-- Pointwise inner-product identity: `∑ᵢ aᵢ · ∂ᵢγ(x) = ⟪a, ∇γ(x)⟫`. The `i`-th directional
derivative `∂ᵢγ = fderiv γ x (eᵢ)` is the `i`-th component of the gradient, so the weighted sum
collapses to the inner product. -/
theorem sum_smul_fderiv_eq_inner {n : ℕ} {γ : (ℝ^n) → ℝ} (hγ : ContDiff ℝ 1 γ) (x : ℝ^n)
    (a : ℝ^n) :
    ∑ i, a i * fderiv ℝ γ x (EuclideanSpace.single i 1) = ⟪a, gradient γ x⟫ := by
  have hg : ∀ i, fderiv ℝ γ x (EuclideanSpace.single i 1) = gradient γ x i := by
    intro i
    rw [← inner_gradient_left (hγ.differentiable (by norm_num) x), PiLp.inner_apply,
      Finset.sum_eq_single i]
    · rw [PiLp.single_apply, if_pos rfl]
      exact (Real.ext_cauchy rfl : (⟪gradient γ x i, (1:ℝ)⟫ : ℝ) = 1 * gradient γ x i).trans (one_mul _)
    · intro j _ hj
      rw [PiLp.single_apply, if_neg hj]
      exact (Real.ext_cauchy rfl : (⟪gradient γ x j, (0:ℝ)⟫ : ℝ) = 0 * gradient γ x j).trans (zero_mul _)
    · simp
  simp_rw [hg]
  rw [PiLp.inner_apply]
  exact Finset.sum_congr rfl fun i _ =>
    ((Real.ext_cauchy rfl : (⟪a i, gradient γ x i⟫ : ℝ) = gradient γ x i * a i).trans (mul_comm _ _)).symm

/-- The divergence of a vector field `F : ℝⁿ × ℝ → ℝⁿ × ℝ` on the ambient half-space: the sum of
the `n` horizontal partials of the horizontal components plus the vertical partial of the vertical
component. -/
noncomputable def divergence {n : ℕ} (F : (ℝ^n) × ℝ → (ℝ^n) × ℝ) (p : (ℝ^n) × ℝ) : ℝ :=
  (∑ i, fderiv ℝ (fun q => (F q).1 i) p (EuclideanSpace.single i 1, 0))
    + fderiv ℝ (fun q => (F q).2) p (0, 1)

set_option linter.style.longLine false in
/-- **Horizontal half of the divergence theorem.** Summing `integral_horizontal_ibp_euclidean`
over the base coordinates: `∑ᵢ ∫ₓ ∫₀^{γx} ∂ᵢFᵢ = −∫ₓ ⟪F₁(x,γx), ∇γ x⟫`, where `F₁` is the
horizontal part of `F`. The per-coordinate boundary terms `∫ Fᵢ(x,γx)·∂ᵢγ` sum to `∫ ⟪F₁,∇γ⟫`
by `sum_smul_fderiv_eq_inner`. -/
theorem horizontal_sum {m : ℕ} {γ : (ℝ^(m + 1)) → ℝ} (hγ : ContDiff ℝ 1 γ)
    {F : (ℝ^(m + 1)) × ℝ → (ℝ^(m + 1)) × ℝ} (hF : ContDiff ℝ 1 F) (hsupp : HasCompactSupport F) :
    ∑ i, (∫ x, ∫ t in (0:ℝ)..(γ x),
        fderiv ℝ (fun q => (F q).1 i) (x, t) (EuclideanSpace.single i 1, 0))
      = - ∫ x, ⟪(F (x, γ x)).1, gradient γ x⟫ := by
  have huc : ∀ i, ContDiff ℝ 1 (fun q => (F q).1 i) :=
    fun i => (contDiff_piLp_apply 2).comp (contDiff_fst.comp hF)
  have husupp : ∀ i, HasCompactSupport (fun q => (F q).1 i) := fun i => by
    have he : (fun q => (F q).1 i) = (fun y : (ℝ^(m + 1)) × ℝ => y.1 i) ∘ F := rfl
    rw [he]; exact hsupp.comp_left (by simp)
  have key : ∀ i, (∫ x, ∫ t in (0:ℝ)..(γ x),
        fderiv ℝ (fun q => (F q).1 i) (x, t) (EuclideanSpace.single i 1, 0))
      = - ∫ x, (F (x, γ x)).1 i * fderiv ℝ γ x (EuclideanSpace.single i 1) :=
    fun i => integral_horizontal_ibp_euclidean i (huc i) hγ (husupp i)
  have hint : ∀ i, Integrable
      (fun x => (F (x, γ x)).1 i * fderiv ℝ γ x (EuclideanSpace.single i 1)) := by
    intro i
    refine Continuous.integrable_of_hasCompactSupport (μ := volume) ?_ ?_
    · exact ((huc i).continuous.comp (continuous_id.prodMk hγ.continuous)).mul
        ((hγ.continuous_fderiv (by norm_num)).clm_apply continuous_const)
    · exact (HasCompactSupport.intro ((husupp i).image continuous_fst)
        (fun x hx => image_eq_zero_of_notMem_tsupport
          (fun hmem => hx ⟨(x, γ x), hmem, rfl⟩))).mul_right
  calc ∑ i, (∫ x, ∫ t in (0:ℝ)..(γ x),
          fderiv ℝ (fun q => (F q).1 i) (x, t) (EuclideanSpace.single i 1, 0))
      = ∑ i, - ∫ x, (F (x, γ x)).1 i * fderiv ℝ γ x (EuclideanSpace.single i 1) :=
        Finset.sum_congr rfl fun i _ => key i
    _ = - ∑ i, ∫ x, (F (x, γ x)).1 i * fderiv ℝ γ x (EuclideanSpace.single i 1) := by
        rw [Finset.sum_neg_distrib]
    _ = - ∫ x, ∑ i, (F (x, γ x)).1 i * fderiv ℝ γ x (EuclideanSpace.single i 1) := by
        rw [← integral_finset_sum _ (fun i _ => hint i)]
    _ = - ∫ x, ⟪(F (x, γ x)).1, gradient γ x⟫ := by
        congr 1
        exact integral_congr_ae (.of_forall fun x => sum_smul_fderiv_eq_inner hγ x (F (x, γ x)).1)

set_option linter.style.longLine false in
/-- **Vertical half of the divergence theorem.** Fibrewise fundamental theorem of calculus for the
vertical partial: `∫ₓ ∫₀^{γx} ∂ₜF₂ = ∫ₓ (F₂(x,γx) − F₂(x,0))`. -/
theorem vertical_ftc {n : ℕ} {γ : (ℝ^n) → ℝ}
    {F : (ℝ^n) × ℝ → (ℝ^n) × ℝ} (hF : ContDiff ℝ 1 F) :
    ∫ x, (∫ t in (0:ℝ)..(γ x), fderiv ℝ (fun q => (F q).2) (x, t) (0, 1))
      = ∫ x, ((F (x, γ x)).2 - (F (x, 0)).2) := by
  have hv : Differentiable ℝ (fun q => (F q).2) := (contDiff_snd.comp hF).differentiable (by norm_num)
  refine integral_congr_ae (.of_forall fun x => ?_)
  dsimp only
  have hslice : ∀ t, HasDerivAt (fun s => (F (x, s)).2)
      (fderiv ℝ (fun q => (F q).2) (x, t) (0, 1)) t := fun t =>
    (hv (x, t)).hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_const t x).prodMk (hasDerivAt_id t))
  have hcontderiv : Continuous (fun t => fderiv ℝ (fun q => (F q).2) (x, t) (0, 1)) :=
    (((contDiff_snd.comp hF).continuous_fderiv (by norm_num)).clm_apply continuous_const).comp
      (continuous_const.prodMk continuous_id)
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hslice t)
    (hcontderiv.intervalIntegrable _ _)

set_option linter.style.longLine false in
/-- **The divergence theorem over the region under a `C¹` graph.** For a `C¹` vector field `F`
with compact support, the iterated volume integral of `div F` over the region under the graph of
`γ` equals the surface flux of `F` through the graph minus the integral of the vertical component
over the flat bottom `{t = 0}`:
`∫ₓ ∫₀^{γx} div F (x,t) dt = ∫_{graph} ⟪F, ν⟫ dμHE − ∫ₓ F₂(x,0)`.
This is the Gauss–Green theorem: the horizontal half (`horizontal_sum`) and the vertical half
(`vertical_ftc`) are added and reconciled with the surface integral via `flux_graph`. -/
theorem divergence_theorem_graph {m : ℕ} {γ : (ℝ^(m + 1)) → ℝ} (hγ : ContDiff ℝ 1 γ)
    {F : (ℝ^(m + 1)) × ℝ → (ℝ^(m + 1)) × ℝ} (hF : ContDiff ℝ 1 F) (hsupp : HasCompactSupport F) :
    (∫ x, ∫ t in (0:ℝ)..(γ x), divergence F (x, t))
      = (∫ y in graphFun γ '' univ, (⟪WithLp.toLp 2 (F y.ofLp), graphNormal γ y.ofLp.1⟫ : ℝ)
            ∂(μHE[m + 1] : Measure (WithLp 2 ((ℝ^(m + 1)) × ℝ))))
          - ∫ x, (F (x, 0)).2 := by
  -- the surface integrand is continuous, hence a.e.-strongly measurable
  have hofLp : Continuous (fun y : WithLp 2 ((ℝ^(m + 1)) × ℝ) => (y.ofLp : (ℝ^(m + 1)) × ℝ)) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ (ℝ^(m + 1)) ℝ).continuous
  have hmeas : AEStronglyMeasurable
      (fun y => ⟪WithLp.toLp 2 (F y.ofLp), graphNormal γ y.ofLp.1⟫)
      ((μHE[m + 1] : Measure (WithLp 2 ((ℝ^(m + 1)) × ℝ))).restrict (graphFun γ '' univ)) :=
    (Continuous.inner
      ((WithLp.prodContinuousLinearEquiv 2 ℝ (ℝ^(m + 1)) ℝ).symm.continuous.comp
        (hF.continuous.comp hofLp))
      ((continuous_graphNormal hγ).comp (continuous_fst.comp hofLp))).aestronglyMeasurable
  -- component smoothness / supports
  have huc : ∀ i, ContDiff ℝ 1 (fun q => (F q).1 i) :=
    fun i => (contDiff_piLp_apply 2).comp (contDiff_fst.comp hF)
  have hvc : ContDiff ℝ 1 (fun q => (F q).2) := contDiff_snd.comp hF
  have husupp : ∀ i, HasCompactSupport (fun q => (F q).1 i) := fun i => by
    have he : (fun q => (F q).1 i) = (fun y : (ℝ^(m + 1)) × ℝ => y.1 i) ∘ F := rfl
    rw [he]; exact hsupp.comp_left (by simp)
  have hvsupp : HasCompactSupport (fun q => (F q).2) := by
    have he : (fun q => (F q).2) = (fun y : (ℝ^(m + 1)) × ℝ => y.2) ∘ F := rfl
    rw [he]; exact hsupp.comp_left (by simp)
  -- continuity of the directional partials as functions on the ambient space
  have hHcont : ∀ i, Continuous
      (fun p : (ℝ^(m + 1)) × ℝ => fderiv ℝ (fun q => (F q).1 i) p (EuclideanSpace.single i 1, 0)) :=
    fun i => ((huc i).continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hVcont : Continuous
      (fun p : (ℝ^(m + 1)) × ℝ => fderiv ℝ (fun q => (F q).2) p (0, 1)) :=
    (hvc.continuous_fderiv (by norm_num)).clm_apply continuous_const
  -- inner interval-integrability (per base point)
  have hHii : ∀ i x, IntervalIntegrable
      (fun t => fderiv ℝ (fun q => (F q).1 i) (x, t) (EuclideanSpace.single i 1, 0)) volume 0 (γ x) :=
    fun i x => ((hHcont i).comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  have hVii : ∀ x, IntervalIntegrable
      (fun t => fderiv ℝ (fun q => (F q).2) (x, t) (0, 1)) volume 0 (γ x) :=
    fun x => (hVcont.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  -- compact support of the partials (for outer integrability)
  have hHsupp : ∀ i, HasCompactSupport
      (fun p : (ℝ^(m + 1)) × ℝ => fderiv ℝ (fun q => (F q).1 i) p (EuclideanSpace.single i 1, 0)) :=
    fun i => (HasCompactSupport.intro ((husupp i).fderiv (𝕜 := ℝ)) (fun p hp => by
      rw [image_eq_zero_of_notMem_tsupport (f := fderiv ℝ (fun q => (F q).1 i)) hp]; rfl))
  have hVsupp : HasCompactSupport
      (fun p : (ℝ^(m + 1)) × ℝ => fderiv ℝ (fun q => (F q).2) p (0, 1)) :=
    HasCompactSupport.intro (hvsupp.fderiv (𝕜 := ℝ)) (fun p hp => by
      rw [image_eq_zero_of_notMem_tsupport (f := fderiv ℝ (fun q => (F q).2)) hp]; rfl)
  -- outer integrability of the fibre integrals (continuous parametric integral, compact support)
  have hHout : ∀ i, Integrable (fun x => ∫ t in (0:ℝ)..(γ x),
      fderiv ℝ (fun q => (F q).1 i) (x, t) (EuclideanSpace.single i 1, 0)) := fun i => by
    refine Continuous.integrable_of_hasCompactSupport (μ := volume)
      (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
        (hHcont i) hγ.continuous) ?_
    refine HasCompactSupport.intro ((hHsupp i).image continuous_fst) (fun x hx => ?_)
    have hz : ∀ t, fderiv ℝ (fun q => (F q).1 i) (x, t) (EuclideanSpace.single i 1, 0) = 0 :=
      fun t => image_eq_zero_of_notMem_tsupport
        (f := fun p => fderiv ℝ (fun q => (F q).1 i) p (EuclideanSpace.single i 1, 0))
        (fun hmem => hx ⟨(x, t), hmem, rfl⟩)
    simp only [hz, intervalIntegral.integral_zero]
  have hVout : Integrable (fun x => ∫ t in (0:ℝ)..(γ x),
      fderiv ℝ (fun q => (F q).2) (x, t) (0, 1)) := by
    refine Continuous.integrable_of_hasCompactSupport (μ := volume)
      (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hVcont hγ.continuous) ?_
    refine HasCompactSupport.intro (hVsupp.image continuous_fst) (fun x hx => ?_)
    have hz : ∀ t, fderiv ℝ (fun q => (F q).2) (x, t) (0, 1) = 0 :=
      fun t => image_eq_zero_of_notMem_tsupport
        (f := fun p => fderiv ℝ (fun q => (F q).2) p (0, 1))
        (fun hmem => hx ⟨(x, t), hmem, rfl⟩)
    simp only [hz, intervalIntegral.integral_zero]
  -- split the fibre integral of the divergence into horizontal sum + vertical
  have hsplit : ∀ x, (∫ t in (0:ℝ)..(γ x), divergence F (x, t))
      = (∑ i, ∫ t in (0:ℝ)..(γ x),
            fderiv ℝ (fun q => (F q).1 i) (x, t) (EuclideanSpace.single i 1, 0))
        + ∫ t in (0:ℝ)..(γ x), fderiv ℝ (fun q => (F q).2) (x, t) (0, 1) := by
    intro x
    have hsumii : IntervalIntegrable (fun t => ∑ i, fderiv ℝ (fun q => (F q).1 i) (x, t)
        (EuclideanSpace.single i 1, 0)) volume 0 (γ x) :=
      (continuous_finset_sum Finset.univ
        (fun i _ => (hHcont i).comp (continuous_const.prodMk continuous_id))).intervalIntegrable _ _
    simp only [divergence]
    rw [intervalIntegral.integral_add hsumii (hVii x),
      intervalIntegral.integral_finset_sum (fun i _ => hHii i x)]
  -- assemble the volume integral
  rw [integral_congr_ae (.of_forall hsplit),
    integral_add (integrable_finset_sum _ (fun i _ => hHout i)) hVout,
    integral_finset_sum _ (fun i _ => hHout i),
    horizontal_sum hγ hF hsupp, vertical_ftc hF]
  -- integrabilities of the three boundary integrands
  have ha : Integrable (fun x => (⟪(F (x, γ x)).1, gradient γ x⟫ : ℝ)) :=
    Continuous.integrable_of_hasCompactSupport (μ := volume)
      (((contDiff_fst.comp hF).continuous.comp (continuous_id.prodMk hγ.continuous)).inner
        (continuous_gradient hγ))
      (HasCompactSupport.intro (hsupp.image continuous_fst) (fun x hx => by
        rw [show (F (x, γ x)).1 = ((0 : (ℝ^(m + 1)) × ℝ)).1 from
          congrArg Prod.fst (image_eq_zero_of_notMem_tsupport
            (fun hmem => hx ⟨(x, γ x), hmem, rfl⟩))]
        simp))
  have hb : Integrable (fun x => (F (x, γ x)).2) :=
    Continuous.integrable_of_hasCompactSupport (μ := volume)
      (hvc.continuous.comp (continuous_id.prodMk hγ.continuous))
      (HasCompactSupport.intro (hsupp.image continuous_fst) (fun x hx => by
        rw [show (F (x, γ x)).2 = ((0 : (ℝ^(m + 1)) × ℝ)).2 from
          congrArg Prod.snd (image_eq_zero_of_notMem_tsupport
            (fun hmem => hx ⟨(x, γ x), hmem, rfl⟩))]
        simp))
  have hc : Integrable (fun x => (F (x, 0)).2) :=
    Continuous.integrable_of_hasCompactSupport (μ := volume)
      (hvc.continuous.comp (continuous_id.prodMk continuous_const))
      (HasCompactSupport.intro (hsupp.image continuous_fst) (fun x hx => by
        rw [show (F (x, 0)).2 = ((0 : (ℝ^(m + 1)) × ℝ)).2 from
          congrArg Prod.snd (image_eq_zero_of_notMem_tsupport
            (fun hmem => hx ⟨(x, 0), hmem, rfl⟩))]
        simp))
  -- relate the boundary integral to the surface flux via `flux_graph`
  have key : (∫ y in graphFun γ '' univ, (⟪WithLp.toLp 2 (F y.ofLp), graphNormal γ y.ofLp.1⟫ : ℝ)
        ∂(μHE[m + 1] : Measure (WithLp 2 ((ℝ^(m + 1)) × ℝ))))
      = ∫ x, ((F (x, γ x)).2 - ⟪(F (x, γ x)).1, gradient γ x⟫) := by
    rw [flux_graph hγ MeasurableSet.univ hmeas, setIntegral_univ]
    rfl
  rw [key, integral_sub hb ha, integral_sub hb hc]
  ring

/-! ### Toward the general divergence theorem: coordinate-free divergence

The graph divergence theorem above is the local building block for the divergence theorem on a
general bounded `C¹` domain (via boundary charts and a partition of unity). The first piece of that
assembly is a coordinate-free divergence on flat Euclidean space and its invariance under the
orthogonal coordinate changes (rotations/reflections) used to straighten the boundary. -/

/-- **Trace as a sum of diagonal inner products** over an orthonormal basis:
`tr A = ∑ᵢ ⟪A eᵢ, eᵢ⟫`. The basis-free engine that makes the divergence (a trace) computable in
any orthonormal frame — both in flat coordinates and the base × height product frame of a graph. -/
theorem trace_eq_sum_inner {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (b : OrthonormalBasis ι ℝ E) (A : E →ₗ[ℝ] E) :
    LinearMap.trace ℝ E A = ∑ i, ⟪A (b i), b i⟫ := by
  rw [LinearMap.trace_eq_matrix_trace ℝ b.toBasis, Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply, real_inner_comm]

/-- The divergence of a vector field on Euclidean space: `div F x = ∑ᵢ ∂ᵢ Fᵢ(x)`, the trace of
the Jacobian. This is the coordinate-free form used for the general divergence theorem. -/
noncomputable def divergenceE {n : ℕ} (F : (ℝ^n) → (ℝ^n)) (x : ℝ^n) : ℝ :=
  ∑ i, fderiv ℝ F x (EuclideanSpace.single i 1) i

set_option linter.style.longLine false in
/-- The divergence is the trace of the Jacobian (basis-free), hence well-defined independently of
the coordinate axes. -/
theorem divergenceE_eq_trace {n : ℕ} (F : (ℝ^n) → (ℝ^n)) (x : ℝ^n) :
    divergenceE F x = LinearMap.trace ℝ _ (fderiv ℝ F x).toLinearMap := by
  rw [divergenceE, LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin n) ℝ).toBasis,
    Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
    EuclideanSpace.basisFun_apply]
  show ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis.repr (fderiv ℝ F x (EuclideanSpace.single i 1))) i
    = fderiv ℝ F x (EuclideanSpace.single i 1) i
  rw [OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr]

/-- **Rotation/reflection invariance of the divergence.** For a linear isometry equivalence `e`
and a differentiable field `F`, the divergence of the conjugated field `y ↦ e⁻¹(F(e y))` at `x`
equals the divergence of `F` at `e x`. The divergence is a scalar invariant of orthogonal
coordinate changes — the key fact that lets boundary charts (rotations straightening `∂Ω` to a
graph) be glued together. -/
theorem divergenceE_comp_isometry {n : ℕ} (e : (ℝ^n) ≃ₗᵢ[ℝ] (ℝ^n)) {F : (ℝ^n) → (ℝ^n)}
    (hF : Differentiable ℝ F) (x : ℝ^n) :
    divergenceE (fun y => e.symm (F (e y))) x = divergenceE F (e x) := by
  have hfd : HasFDerivAt (fun y => e.symm (F (e y)))
      ((e.symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
        ((fderiv ℝ F (e x)).comp e.toContinuousLinearEquiv.toContinuousLinearMap)) x := by
    have h1 : HasFDerivAt (fun y : ℝ^n => e y) e.toContinuousLinearEquiv.toContinuousLinearMap x :=
      e.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt
    have h2 : HasFDerivAt F (fderiv ℝ F (e x)) (e x) := (hF (e x)).hasFDerivAt
    have h3 : HasFDerivAt (fun z : ℝ^n => e.symm z)
        e.symm.toContinuousLinearEquiv.toContinuousLinearMap (F (e x)) :=
      e.symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt
    exact h3.comp x (h2.comp x h1)
  rw [divergenceE_eq_trace, divergenceE_eq_trace, hfd.fderiv]
  have hconj : ((e.symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
      ((fderiv ℝ F (e x)).comp e.toContinuousLinearEquiv.toContinuousLinearMap)).toLinearMap
      = e.toLinearEquiv.symm.conj (fderiv ℝ F (e x)).toLinearMap := rfl
  rw [hconj, LinearMap.trace_conj']

/-- The divergence is additive over finite sums of vector fields — the linearity building block for
the partition-of-unity decomposition `div (Σⱼ gⱼ) = Σⱼ div gⱼ`. -/
theorem divergenceE_finset_sum {n : ℕ} {κ : Type*} (s : Finset κ) (g : κ → (ℝ^n) → (ℝ^n))
    {x : ℝ^n} (hg : ∀ j ∈ s, DifferentiableAt ℝ (g j) x) :
    divergenceE (fun y => ∑ j ∈ s, g j y) x = ∑ j ∈ s, divergenceE (g j) x := by
  simp only [divergenceE]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fderiv_fun_sum hg]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply]
  exact map_sum (EuclideanSpace.proj i) (fun c => fderiv ℝ (g c) x (EuclideanSpace.single i 1)) s

set_option linter.style.longLine false in
/-- **The graph theorem's product divergence is also the trace of the Jacobian.** This identifies
the base × height product divergence `∑ᵢ ∂ᵢFᵢ + ∂ₜF₂` with the basis-free trace, matching
`divergenceE_eq_trace`. It is the bridge that lets the graph divergence theorem be transported into
the canonical flat-coordinate divergence `divergenceE` (via a linear identification of
`(ℝᵐ⁺¹) × ℝ` with `ℝᵐ⁺²`). Proof: trace in the product basis `{(eᵢ,0)} ∪ {(0,1)}`, with each
diagonal entry the corresponding component partial. -/
theorem divergence_eq_trace {m : ℕ} {F : (ℝ^(m + 1)) × ℝ → (ℝ^(m + 1)) × ℝ}
    {p : (ℝ^(m + 1)) × ℝ} (hF : DifferentiableAt ℝ F p) :
    divergence F p = LinearMap.trace ℝ _ (fderiv ℝ F p).toLinearMap := by
  have hc1 : ∀ i, fderiv ℝ (fun q => (F q).1 i) p (EuclideanSpace.single i 1, 0)
      = (fderiv ℝ F p (EuclideanSpace.single i 1, 0)).1 i := fun i => by
    have hclm : fderiv ℝ (fun q => (F q).1 i) p
        = ((EuclideanSpace.proj i).comp (ContinuousLinearMap.fst ℝ (ℝ^(m + 1)) ℝ)).comp
            (fderiv ℝ F p) :=
      (((EuclideanSpace.proj i).comp (ContinuousLinearMap.fst ℝ (ℝ^(m + 1)) ℝ)).hasFDerivAt.comp p
        hF.hasFDerivAt).fderiv
    rw [hclm]; rfl
  have hc2 : fderiv ℝ (fun q => (F q).2) p (0, 1) = (fderiv ℝ F p (0, 1)).2 := by
    have hclm : fderiv ℝ (fun q => (F q).2) p
        = (ContinuousLinearMap.snd ℝ (ℝ^(m + 1)) ℝ).comp (fderiv ℝ F p) :=
      ((ContinuousLinearMap.snd ℝ (ℝ^(m + 1)) ℝ).hasFDerivAt.comp p hF.hasFDerivAt).fderiv
    rw [hclm]; rfl
  rw [divergence]
  simp_rw [hc1, hc2]
  set b := (EuclideanSpace.basisFun (Fin (m + 1)) ℝ).toBasis.prod (Module.Basis.singleton (Fin 1) ℝ)
    with hb
  have hbl : ∀ i, b (Sum.inl i) = (EuclideanSpace.single i (1:ℝ), (0:ℝ)) := by
    intro i; rw [hb, Module.Basis.prod_apply]; simp [EuclideanSpace.basisFun_apply]
  have hbr : ∀ j, b (Sum.inr j) = ((0:ℝ^(m + 1)), (1:ℝ)) := by
    intro j; rw [hb, Module.Basis.prod_apply]; simp
  rw [LinearMap.trace_eq_matrix_trace ℝ b, Matrix.trace, Fintype.sum_sum_type]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.diag, LinearMap.toMatrix_apply, hbl i]
    simp only [ContinuousLinearMap.coe_coe]
    rw [Module.Basis.prod_repr_inl, OrthonormalBasis.coe_toBasis_repr_apply,
      EuclideanSpace.basisFun_repr]
  · rw [Fin.sum_univ_one, Matrix.diag, LinearMap.toMatrix_apply, hbr 0]
    simp only [ContinuousLinearMap.coe_coe]
    rw [Module.Basis.prod_repr_inr, Module.Basis.singleton_repr]

set_option linter.style.longLine false in
/-- **Divergence reconciliation under a coordinate identification.** The canonical flat divergence
`divergenceE` of the conjugated field `z ↦ Φ⁻¹(F(Φ z))` agrees with the graph theorem's product
divergence of `F` at `Φ z`, for any linear identification `Φ : ℝᵐ⁺² ≃L (ℝᵐ⁺¹) × ℝ`. Both are the
trace of the Jacobian (`divergenceE_eq_trace`, `divergence_eq_trace`), and the trace is invariant
under the conjugation by `Φ`. This is the bridge that lets the graph divergence theorem be
restated in flat `EuclideanSpace ℝ (Fin (m+2))` coordinates with the canonical `divergenceE`. -/
theorem divergenceE_comp_cle {m : ℕ} (Φ : (ℝ^(m + 2)) ≃L[ℝ] ((ℝ^(m + 1)) × ℝ))
    {F : (ℝ^(m + 1)) × ℝ → (ℝ^(m + 1)) × ℝ} (hF : Differentiable ℝ F) (y : ℝ^(m + 2)) :
    divergenceE (fun z => Φ.symm (F (Φ z))) y = divergence F (Φ y) := by
  rw [divergenceE_eq_trace, divergence_eq_trace (hF (Φ y))]
  have hfd : HasFDerivAt (fun z => Φ.symm (F (Φ z)))
      ((Φ.symm.toContinuousLinearMap).comp
        ((fderiv ℝ F (Φ y)).comp Φ.toContinuousLinearMap)) y := by
    have h1 : HasFDerivAt (fun z : ℝ^(m + 2) => Φ z) Φ.toContinuousLinearMap y :=
      Φ.toContinuousLinearMap.hasFDerivAt
    have h2 : HasFDerivAt F (fderiv ℝ F (Φ y)) (Φ y) := (hF (Φ y)).hasFDerivAt
    have h3 : HasFDerivAt (fun w => Φ.symm w) Φ.symm.toContinuousLinearMap (F (Φ y)) :=
      Φ.symm.toContinuousLinearMap.hasFDerivAt
    exact h3.comp y (h2.comp y h1)
  rw [hfd.fderiv]
  have hconj : ((Φ.symm.toContinuousLinearMap).comp
      ((fderiv ℝ F (Φ y)).comp Φ.toContinuousLinearMap)).toLinearMap
      = Φ.symm.toLinearEquiv.conj (fderiv ℝ F (Φ y)).toLinearMap := rfl
  rw [hconj, LinearMap.trace_conj']

set_option linter.style.longLine false in
/-- **The flattening isometry.** Identifies the base × height product `WithLp 2 (ℝᵐ⁺¹ × ℝ)` (where
the area formula, surface measure, and flux live) with flat Euclidean space `ℝᵐ⁺²` (where the
general divergence theorem lives), sending the product orthonormal basis `{(eᵢ,0)} ∪ {(0,1)}` to the
standard basis. As a linear isometry equivalence it is automatically volume-preserving
(`LinearIsometryEquiv.measurePreserving`) and surface-measure-preserving
(`Isometry.euclideanHausdorffMeasure_image`), and it preserves inner products — exactly the
properties needed to transport the graph divergence theorem (the volume integral via
`measurePreserving`, the flux via the Hausdorff-measure isometry and `⟪Φ a, Φ b⟫ = ⟪a, b⟫`) into
flat coordinates. -/
noncomputable def flatten (m : ℕ) : WithLp 2 ((ℝ^(m + 1)) × ℝ) ≃ₗᵢ[ℝ] ℝ^(m + 2) :=
  ((EuclideanSpace.basisFun (Fin (m + 1)) ℝ).prod (stdOrthonormalBasis ℝ ℝ)).equiv
    (EuclideanSpace.basisFun (Fin (m + 2)) ℝ)
    ((Equiv.sumCongr (Equiv.refl (Fin (m + 1))) (finCongr (Module.finrank_self ℝ))).trans
      finSumFinEquiv)

/-- The flattening identification as a continuous linear equivalence onto the **plain** product
`(ℝᵐ⁺¹) × ℝ` (the domain of the graph theorem's `divergence`), obtained by composing `flatten` with
the `L²`-product equivalence. This is the `Φ` consumed by `divergenceE_comp_cle` to rewrite the
graph divergence as the flat `divergenceE`. -/
noncomputable def flattenCLE (m : ℕ) : (ℝ^(m + 2)) ≃L[ℝ] ((ℝ^(m + 1)) × ℝ) :=
  (flatten m).symm.toContinuousLinearEquiv.trans
    (WithLp.prodContinuousLinearEquiv 2 ℝ (ℝ^(m + 1)) ℝ)

/-- `flatten` is volume-preserving (it is a linear isometry of finite-dimensional spaces). -/
theorem flatten_measurePreserving (m : ℕ) :
    MeasurePreserving (flatten m) volume volume :=
  (flatten m).measurePreserving

/-- `flatten` preserves the surface (Hausdorff) measure `μHE[m+1]` (it is an isometry). -/
theorem flatten_measurePreserving_μHE (m : ℕ) :
    MeasurePreserving (flatten m)
      (μHE[m + 1] : Measure (WithLp 2 ((ℝ^(m + 1)) × ℝ))) (μHE[m + 1] : Measure (ℝ^(m + 2))) := by
  refine ⟨(flatten m).continuous.measurable, ?_⟩
  ext t ht
  rw [Measure.map_apply (flatten m).continuous.measurable ht,
    ← (flatten m).isometry.euclideanHausdorffMeasure_image ((flatten m) ⁻¹' t),
    Set.image_preimage_eq t (flatten m).surjective]

set_option linter.style.longLine false in
/-- **Volume change of variables under `flatten`**: `∫_{flatten '' s} g = ∫_s g∘flatten`. -/
theorem setIntegral_flatten_image {m : ℕ} (g : (ℝ^(m + 2)) → ℝ)
    (s : Set (WithLp 2 ((ℝ^(m + 1)) × ℝ))) :
    ∫ z in flatten m '' s, g z = ∫ p in s, g (flatten m p) := by
  rw [← (flatten_measurePreserving m).setIntegral_preimage_emb
    (flatten m).toHomeomorph.measurableEmbedding g (flatten m '' s),
    Set.preimage_image_eq s (flatten m).injective]

set_option linter.style.longLine false in
/-- **Surface change of variables under `flatten`**: `∫_{flatten '' s} g dμHE = ∫_s g∘flatten dμHE`. -/
theorem setIntegral_flatten_image_μHE {m : ℕ} (g : (ℝ^(m + 2)) → ℝ)
    (s : Set (WithLp 2 ((ℝ^(m + 1)) × ℝ))) :
    ∫ z in flatten m '' s, g z ∂(μHE[m + 1] : Measure (ℝ^(m + 2)))
      = ∫ p in s, g (flatten m p) ∂(μHE[m + 1] : Measure (WithLp 2 ((ℝ^(m + 1)) × ℝ))) := by
  rw [← (flatten_measurePreserving_μHE m).setIntegral_preimage_emb
    (flatten m).toHomeomorph.measurableEmbedding g (flatten m '' s),
    Set.preimage_image_eq s (flatten m).injective]

set_option linter.style.longLine false in
/-- **Volume change of variables `WithLp` → plain product**: the `L²`-product volume and the plain
product volume agree (via `WithLp.volume_preserving_ofLp`), so an integral over `s ⊆ WithLp 2` of a
plain-product function precomposed with `ofLp` equals the integral over `ofLp '' s`. -/
theorem setIntegral_ofLp {m : ℕ} (f : (ℝ^(m + 1)) × ℝ → ℝ)
    (s : Set (WithLp 2 ((ℝ^(m + 1)) × ℝ))) :
    ∫ p in s, f (WithLp.ofLp p) ∂(volume : Measure (WithLp 2 ((ℝ^(m + 1)) × ℝ)))
      = ∫ q in WithLp.ofLp '' s, f q ∂(volume : Measure ((ℝ^(m + 1)) × ℝ)) := by
  have hemb : MeasurableEmbedding (WithLp.ofLp : WithLp 2 ((ℝ^(m + 1)) × ℝ) → _) :=
    (WithLp.linearEquiv 2 ℝ ((ℝ^(m + 1)) × ℝ)).toContinuousLinearEquiv.toHomeomorph.measurableEmbedding
  rw [← (WithLp.volume_preserving_ofLp (ℝ^(m + 1)) ℝ).setIntegral_preimage_emb hemb f
    (WithLp.ofLp '' s), Set.preimage_image_eq s hemb.injective]

set_option linter.style.longLine false in
/-- **Pointwise divergence bridge.** The flat divergence `divergenceE` of the conjugated field
`z ↦ Φ⁻¹(F(Φ z))` (with `Φ = flattenCLE`), precomposed with `flatten`, is the graph theorem's
product divergence of `F`. Combined with the change-of-variables lemmas this transports the graph
divergence theorem into flat coordinates. -/
theorem divergenceE_flatten {m : ℕ} {F : (ℝ^(m + 1)) × ℝ → (ℝ^(m + 1)) × ℝ}
    (hF : Differentiable ℝ F) (q : WithLp 2 ((ℝ^(m + 1)) × ℝ)) :
    divergenceE (fun z => (flattenCLE m).symm (F (flattenCLE m z))) (flatten m q)
      = divergence F (WithLp.ofLp q) := by
  rw [divergenceE_comp_cle (flattenCLE m) hF (flatten m q)]; congr 1; simp [flattenCLE]

set_option linter.style.longLine false in
/-- **The volume side of the flat divergence theorem.** The volume integral of the flat divergence
`divergenceE` over the flattened subgraph region equals the graph theorem's iterated volume integral
of the product divergence. Assembled from the flatten volume change-of-variables, the pointwise
divergence bridge, the `WithLp → plain` volume bridge, and the Fubini form `setIntegral_regionBetween`
(the region under the `C¹` graph `γ ≥ 0`). -/
theorem setIntegral_flatten_divergence {m : ℕ} {γ : (ℝ^(m + 1)) → ℝ} (hγ : ContDiff ℝ 1 γ)
    (hγ0 : ∀ x, 0 ≤ γ x) {F : (ℝ^(m + 1)) × ℝ → (ℝ^(m + 1)) × ℝ} (hF : ContDiff ℝ 1 F)
    (hsupp : HasCompactSupport F) :
    (∫ z in flatten m ''
        {p : WithLp 2 ((ℝ^(m + 1)) × ℝ) | (WithLp.ofLp p).2 ∈ Set.Ioo 0 (γ (WithLp.ofLp p).1)},
        divergenceE (fun w => (flattenCLE m).symm (F (flattenCLE m w))) z)
      = ∫ x, ∫ t in (0:ℝ)..(γ x), divergence F (x, t) := by
  have hcont : Continuous (fun p => divergence F p) := by
    simp only [divergence]
    refine Continuous.add (continuous_finset_sum _ fun i _ => ?_) ?_
    · exact (((contDiff_piLp_apply 2).comp (contDiff_fst.comp hF)).continuous_fderiv
        (by norm_num)).clm_apply continuous_const
    · exact ((contDiff_snd.comp hF).continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hcs : HasCompactSupport (fun p => divergence F p) := by
    apply HasCompactSupport.intro (hsupp.fderiv (𝕜 := ℝ))
    intro p hp
    have hfp : fderiv ℝ F p = 0 := image_eq_zero_of_notMem_tsupport hp
    simp only [divergence]
    have h1 : ∀ i, fderiv ℝ (fun q => (F q).1 i) p (EuclideanSpace.single i 1, 0) = 0 := fun i => by
      have hclm : fderiv ℝ (fun q => (F q).1 i) p
          = ((EuclideanSpace.proj i).comp (ContinuousLinearMap.fst ℝ (ℝ^(m + 1)) ℝ)).comp
              (fderiv ℝ F p) :=
        (((EuclideanSpace.proj i).comp (ContinuousLinearMap.fst ℝ (ℝ^(m + 1)) ℝ)).hasFDerivAt.comp p
          (hF.differentiable (by norm_num) p).hasFDerivAt).fderiv
      rw [hclm, hfp]; simp
    have h2 : fderiv ℝ (fun q => (F q).2) p (0, 1) = 0 := by
      have hclm : fderiv ℝ (fun q => (F q).2) p
          = (ContinuousLinearMap.snd ℝ (ℝ^(m + 1)) ℝ).comp (fderiv ℝ F p) :=
        ((ContinuousLinearMap.snd ℝ (ℝ^(m + 1)) ℝ).hasFDerivAt.comp p
          (hF.differentiable (by norm_num) p).hasFDerivAt).fderiv
      rw [hclm, hfp]; simp
    simp [h1, h2]
  have hint : IntegrableOn (fun p => divergence F p) (regionBetween (fun _ => (0:ℝ)) γ univ) :=
    (hcont.integrable_of_hasCompactSupport hcs).integrableOn
  rw [setIntegral_flatten_image]
  simp_rw [divergenceE_flatten (hF.differentiable (by norm_num))]
  rw [setIntegral_ofLp]
  have hset : WithLp.ofLp ''
      {p : WithLp 2 ((ℝ^(m + 1)) × ℝ) | (WithLp.ofLp p).2 ∈ Set.Ioo 0 (γ (WithLp.ofLp p).1)}
      = regionBetween (fun _ => (0:ℝ)) γ univ := by
    ext q
    simp only [Set.mem_image, Set.mem_setOf_eq, regionBetween, Set.mem_univ, true_and]
    constructor
    · rintro ⟨p, hp, rfl⟩; exact hp
    · intro hq; exact ⟨WithLp.toLp 2 q, hq, rfl⟩
  rw [hset, setIntegral_regionBetween hγ.continuous.measurable MeasurableSet.univ hint,
    setIntegral_univ]
  refine integral_congr_ae (.of_forall fun x => ?_)
  dsimp only
  rw [intervalIntegral.integral_of_le (hγ0 x), integral_Ioc_eq_integral_Ioo]

set_option linter.style.longLine false in
/-- **The surface (flux) side of the flat divergence theorem.** The surface flux of the flat field
against the flat normal, over the flattened graph, equals the graph theorem's surface flux. Uses the
`flatten` surface change-of-variables and the fact that `flatten`, an isometry, preserves inner
products. -/
theorem setIntegral_flatten_flux {m : ℕ} {γ : (ℝ^(m + 1)) → ℝ}
    {F : (ℝ^(m + 1)) × ℝ → (ℝ^(m + 1)) × ℝ} :
    (∫ z in flatten m '' (graphFun γ '' univ),
        (⟪(flattenCLE m).symm (F (flattenCLE m z)),
            flatten m (graphNormal γ ((flatten m).symm z).ofLp.1)⟫ : ℝ)
          ∂(μHE[m + 1] : Measure (ℝ^(m + 2))))
      = ∫ y in graphFun γ '' univ, (⟪WithLp.toLp 2 (F y.ofLp), graphNormal γ y.ofLp.1⟫ : ℝ)
          ∂(μHE[m + 1] : Measure (WithLp 2 ((ℝ^(m + 1)) × ℝ))) := by
  rw [setIntegral_flatten_image_μHE]
  refine integral_congr_ae (.of_forall fun y => ?_)
  dsimp only
  rw [LinearIsometryEquiv.symm_apply_apply,
    show (flattenCLE m).symm (F (flattenCLE m (flatten m y)))
      = flatten m (WithLp.toLp 2 (F (WithLp.ofLp y))) from by simp [flattenCLE],
    LinearIsometryEquiv.inner_map_map]

set_option linter.style.longLine false in
/-- **The divergence theorem in flat `ℝᵐ⁺²` coordinates.** For a `C¹` compactly-supported field `F`
and a `C¹` graph `γ ≥ 0`, the volume integral of the canonical flat divergence `divergenceE` over
the flattened subgraph region equals the surface flux through the flattened graph minus the
flat-bottom term. This is the graph divergence theorem (`divergence_theorem_graph`) transported via
the flattening isometry `flatten` into flat Euclidean coordinates with the canonical divergence —
the local building block for the general divergence theorem on a bounded `C¹` domain. -/
theorem divergence_theorem_flat {m : ℕ} {γ : (ℝ^(m + 1)) → ℝ} (hγ : ContDiff ℝ 1 γ)
    (hγ0 : ∀ x, 0 ≤ γ x) {F : (ℝ^(m + 1)) × ℝ → (ℝ^(m + 1)) × ℝ} (hF : ContDiff ℝ 1 F)
    (hsupp : HasCompactSupport F) :
    (∫ z in flatten m ''
        {p : WithLp 2 ((ℝ^(m + 1)) × ℝ) | (WithLp.ofLp p).2 ∈ Set.Ioo 0 (γ (WithLp.ofLp p).1)},
        divergenceE (fun w => (flattenCLE m).symm (F (flattenCLE m w))) z)
      = (∫ z in flatten m '' (graphFun γ '' univ),
            (⟪(flattenCLE m).symm (F (flattenCLE m z)),
                flatten m (graphNormal γ ((flatten m).symm z).ofLp.1)⟫ : ℝ)
              ∂(μHE[m + 1] : Measure (ℝ^(m + 2))))
          - ∫ x, (F (x, 0)).2 := by
  rw [setIntegral_flatten_divergence hγ hγ0 hF hsupp, divergence_theorem_graph hγ hF hsupp,
    ← setIntegral_flatten_flux]

set_option linter.style.longLine false in
/-- **The divergence theorem for a compactly-supported field on all of `ℝᵐ⁺¹`**: `∫ div F = 0`.
The interior case of the partition-of-unity assembly (a field supported in the interior of a domain
contributes no boundary flux). Each `∫ ∂ᵢFᵢ = 0` by Fubini plus the compact-support fundamental
theorem of calculus, bridged from the pi type to `EuclideanSpace`. -/
theorem integral_divergenceE_eq_zero {m : ℕ} {F : (ℝ^(m + 1)) → (ℝ^(m + 1))}
    (hF : ContDiff ℝ 1 F) (hsupp : HasCompactSupport F) :
    ∫ x, divergenceE F x = 0 := by
  have hFd : Differentiable ℝ F := hF.differentiable (by norm_num)
  set e : (Fin (m + 1) → ℝ) ≃L[ℝ] ℝ^(m + 1) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (m + 1) => ℝ)).symm with he
  have hmp : MeasureTheory.MeasurePreserving e := PiLp.volume_preserving_toLp (Fin (m + 1))
  have hme : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  have hcont : ∀ i, Continuous
      (fun x : ℝ^(m + 1) => (fderiv ℝ F x (EuclideanSpace.single i 1)).ofLp i) := fun i =>
    (EuclideanSpace.proj i).continuous.comp
      ((hF.continuous_fderiv (by norm_num)).clm_apply continuous_const)
  have hcs : ∀ i, HasCompactSupport
      (fun x : ℝ^(m + 1) => (fderiv ℝ F x (EuclideanSpace.single i 1)).ofLp i) := fun i =>
    HasCompactSupport.intro (hsupp.fderiv (𝕜 := ℝ)) (fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport (f := fderiv ℝ F) hx]; rfl)
  have hint : ∀ i, Integrable
      (fun x : ℝ^(m + 1) => (fderiv ℝ F x (EuclideanSpace.single i 1)).ofLp i) := fun i =>
    (hcont i).integrable_of_hasCompactSupport (hcs i)
  simp only [divergenceE]
  rw [integral_finset_sum _ (fun i _ => hint i)]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [← hmp.integral_comp hme (fun x => (fderiv ℝ F x (EuclideanSpace.single i 1)).ofLp i)]
  refine integral_eq_zero_of_forall_insertNth_integral_zero i
    (((hcont i).comp e.continuous).integrable_of_hasCompactSupport
      ((hcs i).comp_homeomorph e.toHomeomorph)) (fun y => ?_)
  have hchain : ∀ s, HasDerivAt (fun s' => (F (e (i.insertNth s' y))).ofLp i)
      ((fderiv ℝ F (e (i.insertNth s y)) (EuclideanSpace.single i 1)).ofLp i) s := fun s => by
    have h1 : HasDerivAt (fun s' => (i.insertNth s' y : Fin (m + 1) → ℝ)) (Pi.single i 1) s :=
      hasDerivAt_insertNth i y s
    have h2 := (hFd (e (i.insertNth s y))).hasFDerivAt.comp_hasDerivAt s
      (e.hasFDerivAt.comp_hasDerivAt s h1)
    exact (EuclideanSpace.proj i).hasFDerivAt.comp_hasDerivAt s h2
  have hemb : Topology.IsClosedEmbedding (fun s => e (i.insertNth s y)) :=
    e.toHomeomorph.isClosedEmbedding.comp (isClosedEmbedding_insertNth i y)
  have hslicecs : HasCompactSupport (fun s' => (F (e (i.insertNth s' y))).ofLp i) :=
    (hsupp.comp_isClosedEmbedding hemb).comp_left (g := fun w : ℝ^(m + 1) => w.ofLp i) rfl
  have hslicecd : ContDiff ℝ 1 (fun s' => (F (e (i.insertNth s' y))).ofLp i) := by
    exact (EuclideanSpace.proj i).contDiff.comp
      (hF.comp (e.contDiff.comp (contDiff_insertNth i y)))
  simp_rw [fun s => (hchain s).deriv.symm]
  exact integral_deriv_eq_zero hslicecd hslicecs

/-! ### Bounded `C¹` domains

The domain of the general divergence theorem: an open bounded set whose boundary is, near each of
its points, a `C¹` graph in a suitably rotated and translated frame. The boundary is compact (the
key to extracting a finite chart cover for the partition-of-unity assembly). -/

set_option linter.style.longLine false in
/-- A **bounded `C¹` domain** in `ℝᵐ⁺²`: open, bounded, with boundary locally a `C¹` graph. Near
each boundary point `x₀` there are a radius `r`, a rotation `e`, and a `C¹` function `γ` such that,
in the rotated-and-translated frame (`x ↦ (flatten).symm (e (x − x₀))`, splitting `ℝᵐ⁺²` into
base × height), the domain is exactly the strict subgraph `height < γ(base)`. This is Evans' local
boundary-flattening hypothesis (§C.1), with `flatten` providing the base × height split. -/
structure IsBoundedC1Domain {m : ℕ} (Ω : Set (ℝ^(m + 2))) : Prop where
  /-- The domain is open. -/
  isOpen : IsOpen Ω
  /-- The domain is bounded (so its closure is compact). -/
  isBounded : Bornology.IsBounded Ω
  /-- The boundary is, near each point, a `C¹` graph in a rotated/translated frame. -/
  locallyGraph : ∀ x₀ ∈ frontier Ω, ∃ (r : ℝ) (_ : 0 < r) (e : (ℝ^(m + 2)) ≃ₗᵢ[ℝ] (ℝ^(m + 2)))
    (γ : (ℝ^(m + 1)) → ℝ), ContDiff ℝ 1 γ ∧
    Ω ∩ Metric.ball x₀ r =
      {x | ((flatten m).symm (e (x - x₀))).ofLp.2 < γ ((flatten m).symm (e (x - x₀))).ofLp.1}
        ∩ Metric.ball x₀ r

namespace IsBoundedC1Domain
variable {m : ℕ} {Ω : Set (ℝ^(m + 2))}

/-- A bounded `C¹` domain is measurable. -/
theorem measurableSet (h : IsBoundedC1Domain Ω) : MeasurableSet Ω := h.isOpen.measurableSet

/-- The closure of a bounded `C¹` domain is compact. -/
theorem isCompact_closure (h : IsBoundedC1Domain Ω) : IsCompact (closure Ω) :=
  h.isBounded.isCompact_closure

/-- **The boundary of a bounded `C¹` domain is compact** — the finiteness behind the partition of
unity that assembles the general divergence theorem from the local graph charts. -/
theorem isCompact_frontier (h : IsBoundedC1Domain Ω) : IsCompact (frontier Ω) :=
  h.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure

set_option linter.style.longLine false in
/-- **Finite chart cover of the boundary.** The compact boundary of a bounded `C¹` domain is
covered by finitely many chart balls, each carrying its rotation `e` and graph `γ` in which `Ω` is
locally a subgraph. Extracted from `isCompact_frontier` and the local-graph hypothesis; this is the
finite cover underlying the partition-of-unity assembly of the general divergence theorem. -/
theorem exists_finite_chart_cover (h : IsBoundedC1Domain Ω) :
    ∃ (ι : Type) (_ : Fintype ι) (c : ι → ℝ^(m + 2)) (r : ι → ℝ),
      (∀ j, 0 < r j) ∧ (frontier Ω ⊆ ⋃ j, Metric.ball (c j) (r j)) ∧
      (∀ j, ∃ (e : (ℝ^(m + 2)) ≃ₗᵢ[ℝ] (ℝ^(m + 2))) (γ : (ℝ^(m + 1)) → ℝ), ContDiff ℝ 1 γ ∧
        Ω ∩ Metric.ball (c j) (r j) =
          {x | ((flatten m).symm (e (x - c j))).ofLp.2 < γ ((flatten m).symm (e (x - c j))).ofLp.1}
            ∩ Metric.ball (c j) (r j)) := by
  choose ρ hρpos e γ hchart using h.locallyGraph
  set U : ↥(frontier Ω) → Set (ℝ^(m + 2)) := fun p => Metric.ball ↑p (ρ ↑p p.2) with hU
  have hcover : frontier Ω ⊆ ⋃ p, U p := fun x hx =>
    Set.mem_iUnion.2 ⟨⟨x, hx⟩, Metric.mem_ball_self (hρpos x hx)⟩
  obtain ⟨t, ht⟩ := h.isCompact_frontier.elim_finite_subcover U
    (fun p => Metric.isOpen_ball) hcover
  refine ⟨↥t, inferInstance, fun j => j.1.1, fun j => ρ j.1.1 j.1.2,
    fun j => hρpos j.1.1 j.1.2, ?_,
    fun j => ⟨e j.1.1 j.1.2, γ j.1.1 j.1.2, (hchart j.1.1 j.1.2).1, (hchart j.1.1 j.1.2).2⟩⟩
  refine ht.trans (Set.iUnion₂_subset fun p hp => ?_)
  exact Set.subset_iUnion_of_subset ⟨p, hp⟩ (le_refl _)

set_option linter.style.longLine false in
/-- **Partition of unity for the domain.** A smooth partition of unity on `closure Ω` subordinate to
the cover `{Ω} ∪ {chart balls}` (indexed by `Option ι`: `none` ↦ the interior `Ω`, `some j` ↦ the
`j`-th boundary chart ball). This is the device that splits a field into an interior piece plus
boundary-chart pieces for the partition-of-unity assembly of the general divergence theorem. -/
theorem exists_smoothPartitionOfUnity (h : IsBoundedC1Domain Ω) :
    ∃ (ι : Type) (_ : Fintype ι) (c : ι → ℝ^(m + 2)) (r : ι → ℝ),
      (∀ j, 0 < r j) ∧
      (∀ j, ∃ (e : (ℝ^(m + 2)) ≃ₗᵢ[ℝ] (ℝ^(m + 2))) (γ : (ℝ^(m + 1)) → ℝ), ContDiff ℝ 1 γ ∧
        Ω ∩ Metric.ball (c j) (r j) =
          {x | ((flatten m).symm (e (x - c j))).ofLp.2 < γ ((flatten m).symm (e (x - c j))).ofLp.1}
            ∩ Metric.ball (c j) (r j)) ∧
      ∃ f : SmoothPartitionOfUnity (Option ι) (𝓘(ℝ, ℝ^(m + 2))) (ℝ^(m + 2)) (closure Ω),
        f.IsSubordinate (fun i => i.elim Ω (fun j => Metric.ball (c j) (r j))) := by
  obtain ⟨ι, hFin, c, r, hr, hcov, hcharts⟩ := h.exists_finite_chart_cover
  refine ⟨ι, hFin, c, r, hr, hcharts, ?_⟩
  set U : Option ι → Set (ℝ^(m + 2)) := fun i => i.elim Ω (fun j => Metric.ball (c j) (r j)) with hUdef
  have hUopen : ∀ i, IsOpen (U i) := by rintro (_ | j); exacts [h.isOpen, Metric.isOpen_ball]
  have hcovcl : closure Ω ⊆ ⋃ i, U i := fun x hx => by
    by_cases hxΩ : x ∈ Ω
    · exact Set.mem_iUnion.2 ⟨none, hxΩ⟩
    · have hxf : x ∈ frontier Ω := ⟨hx, fun hc => hxΩ (h.isOpen.interior_eq ▸ hc)⟩
      obtain ⟨j, hxj⟩ := Set.mem_iUnion.1 (hcov hxf)
      exact Set.mem_iUnion.2 ⟨some j, hxj⟩
  exact SmoothPartitionOfUnity.exists_isSubordinate (𝓘(ℝ, ℝ^(m + 2))) isClosed_closure U hUopen
    hcovcl

end IsBoundedC1Domain

set_option linter.style.longLine false

/-- The integral of a single diagonal partial `∂ᵢFᵢ` of a compactly-supported `C¹` field over all
of `ℝᵐ⁺¹` vanishes (the per-coordinate interior divergence-zero; the atom behind the half-space
slab term of the chart flux). -/
theorem integral_component_deriv_eq_zero {m : ℕ} {F : (ℝ^(m + 1)) → (ℝ^(m + 1))}
    (hF : ContDiff ℝ 1 F) (hsupp : HasCompactSupport F) (i : Fin (m + 1)) :
    ∫ x, (fderiv ℝ F x (EuclideanSpace.single i 1)).ofLp i = 0 := by
  have hFd : Differentiable ℝ F := hF.differentiable (by norm_num)
  set e : (Fin (m + 1) → ℝ) ≃L[ℝ] ℝ^(m + 1) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (m + 1) => ℝ)).symm with he
  have hmp : MeasureTheory.MeasurePreserving e := PiLp.volume_preserving_toLp (Fin (m + 1))
  have hme : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  have hcont : Continuous
      (fun x : ℝ^(m + 1) => (fderiv ℝ F x (EuclideanSpace.single i 1)).ofLp i) :=
    (EuclideanSpace.proj i).continuous.comp
      ((hF.continuous_fderiv (by norm_num)).clm_apply continuous_const)
  have hcs : HasCompactSupport
      (fun x : ℝ^(m + 1) => (fderiv ℝ F x (EuclideanSpace.single i 1)).ofLp i) :=
    HasCompactSupport.intro (hsupp.fderiv (𝕜 := ℝ)) (fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport (f := fderiv ℝ F) hx]; rfl)
  rw [← hmp.integral_comp hme (fun x => (fderiv ℝ F x (EuclideanSpace.single i 1)).ofLp i)]
  refine integral_eq_zero_of_forall_insertNth_integral_zero i
    ((hcont.comp e.continuous).integrable_of_hasCompactSupport
      (hcs.comp_homeomorph e.toHomeomorph)) (fun y => ?_)
  have hchain : ∀ s, HasDerivAt (fun s' => (F (e (i.insertNth s' y))).ofLp i)
      ((fderiv ℝ F (e (i.insertNth s y)) (EuclideanSpace.single i 1)).ofLp i) s := fun s => by
    have h1 : HasDerivAt (fun s' => (i.insertNth s' y : Fin (m + 1) → ℝ)) (Pi.single i 1) s :=
      hasDerivAt_insertNth i y s
    have h2 := (hFd (e (i.insertNth s y))).hasFDerivAt.comp_hasDerivAt s
      (e.hasFDerivAt.comp_hasDerivAt s h1)
    exact (EuclideanSpace.proj i).hasFDerivAt.comp_hasDerivAt s h2
  have hemb : Topology.IsClosedEmbedding (fun s => e (i.insertNth s y)) :=
    e.toHomeomorph.isClosedEmbedding.comp (isClosedEmbedding_insertNth i y)
  have hslicecs : HasCompactSupport (fun s' => (F (e (i.insertNth s' y))).ofLp i) :=
    (hsupp.comp_isClosedEmbedding hemb).comp_left (g := fun w : ℝ^(m + 1) => w.ofLp i) rfl
  have hslicecd : ContDiff ℝ 1 (fun s' => (F (e (i.insertNth s' y))).ofLp i) := by
    exact (EuclideanSpace.proj i).contDiff.comp
      (hF.comp (e.contDiff.comp (contDiff_insertNth i y)))
  simp_rw [fun s => (hchain s).deriv.symm]
  exact integral_deriv_eq_zero hslicecd hslicecs

/-- Base-slice horizontal zero: at fixed height `t`, `∫ₓ ∂ᵢFᵢ(x,t) dx = 0`. Reduces to
`integral_component_deriv_eq_zero` on the base-slice field `x ↦ (F(x,t)).1`. -/
theorem integral_base_slice_deriv_eq_zero {m : ℕ} {F : (ℝ^(m + 1)) × ℝ → (ℝ^(m + 1)) × ℝ}
    (hF : ContDiff ℝ 1 F) (hsupp : HasCompactSupport F) (i : Fin (m + 1)) (t : ℝ) :
    ∫ x, fderiv ℝ (fun q => (F q).1 i) (x, t) (EuclideanSpace.single i 1, 0) = 0 := by
  have hslice_cd : ContDiff ℝ 1 (fun x : ℝ^(m + 1) => (F (x, t)).1) :=
    (contDiff_fst.comp hF).comp (contDiff_id.prodMk contDiff_const)
  have hslice_cs : HasCompactSupport (fun x : ℝ^(m + 1) => (F (x, t)).1) :=
    HasCompactSupport.intro (hsupp.image continuous_fst) (fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport (f := F) (fun hmem => hx ⟨(x, t), hmem, rfl⟩)]; rfl)
  have hcomp : ∀ x : ℝ^(m + 1),
      fderiv ℝ (fun q => (F q).1 i) (x, t) (EuclideanSpace.single i 1, 0)
        = (fderiv ℝ (fun x' => (F (x', t)).1) x (EuclideanSpace.single i 1)).ofLp i := by
    intro x
    have hL : fderiv ℝ (fun q => (F q).1 i) (x, t)
        = ((EuclideanSpace.proj i).comp (ContinuousLinearMap.fst ℝ (ℝ^(m + 1)) ℝ)).comp
            (fderiv ℝ F (x, t)) :=
      (((EuclideanSpace.proj i).comp (ContinuousLinearMap.fst ℝ (ℝ^(m + 1)) ℝ)).hasFDerivAt.comp
        (x, t) (hF.differentiable (by norm_num) (x, t)).hasFDerivAt).fderiv
    have hslice_fderiv : HasFDerivAt (fun x' : ℝ^(m + 1) => ((x', t) : (ℝ^(m + 1)) × ℝ))
        ((ContinuousLinearMap.id ℝ (ℝ^(m + 1))).prod 0) x :=
      (hasFDerivAt_id x).prodMk (hasFDerivAt_const t x)
    have hR : fderiv ℝ (fun x' : ℝ^(m + 1) => (F (x', t)).1) x
        = (ContinuousLinearMap.fst ℝ (ℝ^(m + 1)) ℝ).comp
            ((fderiv ℝ F (x, t)).comp ((ContinuousLinearMap.id ℝ (ℝ^(m + 1))).prod 0)) :=
      ((ContinuousLinearMap.fst ℝ (ℝ^(m + 1)) ℝ).hasFDerivAt.comp x
        ((hF.differentiable (by norm_num) (x, t)).hasFDerivAt.comp x hslice_fderiv)).fderiv
    rw [hL, hR]; rfl
  simp_rw [hcomp]
  exact integral_component_deriv_eq_zero hslice_cd hslice_cs i

/-- Slab horizontal zero: `∫ₓ ∫_{t≤0} ∂ᵢFᵢ(x,t) = 0` (Fubini + the base-slice atom). -/
theorem integral_Iic_base_deriv_eq_zero {m : ℕ} {F : (ℝ^(m + 1)) × ℝ → (ℝ^(m + 1)) × ℝ} (hF : ContDiff ℝ 1 F)
    (hsupp : HasCompactSupport F) (i : Fin (m + 1)) :
    ∫ x, ∫ t in Set.Iic (0:ℝ), fderiv ℝ (fun q => (F q).1 i) (x, t) (EuclideanSpace.single i 1, 0) = 0 := by
  have hcont : Continuous (fun p : (ℝ^(m+1)) × ℝ => fderiv ℝ (fun q => (F q).1 i) p (EuclideanSpace.single i 1, 0)) :=
    ((contDiff_piLp_apply 2).comp (contDiff_fst.comp hF)).continuous_fderiv (by norm_num) |>.clm_apply continuous_const
  have hcs : HasCompactSupport (fun p : (ℝ^(m+1)) × ℝ => fderiv ℝ (fun q => (F q).1 i) p (EuclideanSpace.single i 1, 0)) := by
    apply HasCompactSupport.intro (((hsupp.comp_left (g := fun w : (ℝ^(m+1)) × ℝ => w.1 i) (by simp)).fderiv (𝕜 := ℝ)))
    intro p hp
    rw [image_eq_zero_of_notMem_tsupport (f := fun p => fderiv ℝ (fun q => (F q).1 i) p) (fun hmem => hp hmem)]
    rfl
  have hint : Integrable (Function.uncurry (fun (x : ℝ^(m+1)) (t : ℝ) => fderiv ℝ (fun q => (F q).1 i) (x, t) (EuclideanSpace.single i 1, 0))) (volume.prod (volume.restrict (Set.Iic (0:ℝ)))) := by
    have hfull := hcont.integrable_of_hasCompactSupport (μ := volume) hcs
    rw [Measure.volume_eq_prod] at hfull
    have hmeq : (volume : Measure (ℝ^(m + 1))).prod (volume.restrict (Set.Iic (0:ℝ)))
        = ((volume : Measure (ℝ^(m + 1))).prod volume).restrict (Set.univ ×ˢ Set.Iic 0) := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]
    rw [hmeq]
    exact hfull.restrict
  rw [MeasureTheory.integral_integral_swap hint]
  simp_rw [integral_base_slice_deriv_eq_zero hF hsupp i, integral_zero]

/-- Slab vertical: `∫ₓ ∫_{t≤0} ∂ₜF₂(x,t) = ∫ₓ F₂(x,0)` via the compact-support FTC over `Iic`. -/
theorem integral_Iic_vert_deriv_eq {m : ℕ} {F : (ℝ^(m + 1)) × ℝ → (ℝ^(m + 1)) × ℝ}
    (hF : ContDiff ℝ 1 F) (hsupp : HasCompactSupport F) :
    ∫ x, ∫ t in Set.Iic (0:ℝ), fderiv ℝ (fun q => (F q).2) (x, t) (0, 1) = ∫ x, (F (x, 0)).2 := by
  refine integral_congr_ae (.of_forall fun x => ?_)
  have hsl_cd : ContDiff ℝ 1 (fun t' : ℝ => (F (x, t')).2) :=
    (contDiff_snd.comp hF).comp (contDiff_const.prodMk contDiff_id)
  have hsl_cs : HasCompactSupport (fun t' : ℝ => (F (x, t')).2) :=
    HasCompactSupport.intro (hsupp.image continuous_snd) (fun t' ht' => by
      rw [image_eq_zero_of_notMem_tsupport (f := F) (fun hmem => ht' ⟨(x, t'), hmem, rfl⟩)]; rfl)
  have hchain : ∀ t, fderiv ℝ (fun q => (F q).2) (x, t) (0, 1)
      = deriv (fun t' => (F (x, t')).2) t := fun t => by
    have hsl_fderiv : HasFDerivAt (fun t' : ℝ => ((x, t') : (ℝ^(m + 1)) × ℝ))
        ((0 : ℝ →L[ℝ] (ℝ^(m + 1))).prod (ContinuousLinearMap.id ℝ ℝ)) t :=
      (hasFDerivAt_const x t).prodMk (hasFDerivAt_id t)
    have : HasDerivAt (fun t' => (F (x, t')).2)
        (fderiv ℝ (fun q => (F q).2) (x, t) (0, 1)) t := by
      have h2 : Differentiable ℝ (fun q => (F q).2) := (contDiff_snd.comp hF).differentiable (by norm_num)
      exact (h2 (x, t)).hasFDerivAt.comp_hasDerivAt t (hsl_fderiv.hasDerivAt)
    exact (this.deriv).symm
  simp_rw [hchain]
  exact HasCompactSupport.integral_Iic_deriv_eq hsl_cd hsl_cs 0

/-- **Half-space slab divergence theorem** (iterated form): `∫ₓ ∫_{t≤0} div F = ∫ₓ F₂(x,0)`.
Swap the divergence integral (Fubini), reduce each height-slice to its vertical part via
`integral_base_slice_deriv_eq_zero`, and swap back for the `Iic` fundamental theorem of calculus. -/
theorem integral_Iic_divergence_eq {m : ℕ} {F : (ℝ^(m + 1)) × ℝ → (ℝ^(m + 1)) × ℝ}
    (hF : ContDiff ℝ 1 F) (hsupp : HasCompactSupport F) :
    ∫ x, ∫ t in Set.Iic (0:ℝ), divergence F (x, t) = ∫ x, (F (x, 0)).2 := by
  -- continuity + compact support of the divergence and of the vertical partial
  have huc : ∀ i, ContDiff ℝ 1 (fun q => (F q).1 i) :=
    fun i => (contDiff_piLp_apply 2).comp (contDiff_fst.comp hF)
  have hvc : ContDiff ℝ 1 (fun q => (F q).2) := contDiff_snd.comp hF
  have hHcont : ∀ i, Continuous (fun p : (ℝ^(m+1)) × ℝ => fderiv ℝ (fun q => (F q).1 i) p (EuclideanSpace.single i 1, 0)) :=
    fun i => ((huc i).continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hVcont : Continuous (fun p : (ℝ^(m+1)) × ℝ => fderiv ℝ (fun q => (F q).2) p (0, 1)) :=
    (hvc.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hHcs : ∀ i, HasCompactSupport (fun p : (ℝ^(m+1)) × ℝ => fderiv ℝ (fun q => (F q).1 i) p (EuclideanSpace.single i 1, 0)) :=
    fun i => HasCompactSupport.intro ((hsupp.comp_left (g := fun w : (ℝ^(m+1)) × ℝ => w.1 i) (by simp)).fderiv (𝕜 := ℝ))
      (fun p hp => by rw [image_eq_zero_of_notMem_tsupport (f := fun p => fderiv ℝ (fun q => (F q).1 i) p) hp]; rfl)
  have hVcs : HasCompactSupport (fun p : (ℝ^(m+1)) × ℝ => fderiv ℝ (fun q => (F q).2) p (0, 1)) :=
    HasCompactSupport.intro ((hsupp.comp_left (g := fun w : (ℝ^(m+1)) × ℝ => w.2) rfl).fderiv (𝕜 := ℝ))
      (fun p hp => by rw [image_eq_zero_of_notMem_tsupport (f := fun p => fderiv ℝ (fun q => (F q).2) p) hp]; rfl)
  have hdivcont : Continuous (fun p => divergence F p) := by
    simp only [divergence]
    exact (continuous_finset_sum _ fun i _ => hHcont i).add hVcont
  have hdivcs : HasCompactSupport (fun p => divergence F p) := by
    apply HasCompactSupport.intro (hsupp.fderiv (𝕜 := ℝ))
    intro p hp
    have hfp : fderiv ℝ F p = 0 := image_eq_zero_of_notMem_tsupport hp
    simp only [divergence]
    have h1 : ∀ i, fderiv ℝ (fun q => (F q).1 i) p (EuclideanSpace.single i 1, 0) = 0 := fun i => by
      have hclm : fderiv ℝ (fun q => (F q).1 i) p = ((EuclideanSpace.proj i).comp (ContinuousLinearMap.fst ℝ (ℝ^(m+1)) ℝ)).comp (fderiv ℝ F p) :=
        (((EuclideanSpace.proj i).comp (ContinuousLinearMap.fst ℝ (ℝ^(m+1)) ℝ)).hasFDerivAt.comp p (hF.differentiable (by norm_num) p).hasFDerivAt).fderiv
      rw [hclm, hfp]; simp
    have h2 : fderiv ℝ (fun q => (F q).2) p (0, 1) = 0 := by
      have hclm : fderiv ℝ (fun q => (F q).2) p = (ContinuousLinearMap.snd ℝ (ℝ^(m+1)) ℝ).comp (fderiv ℝ F p) :=
        ((ContinuousLinearMap.snd ℝ (ℝ^(m+1)) ℝ).hasFDerivAt.comp p (hF.differentiable (by norm_num) p).hasFDerivAt).fderiv
      rw [hclm, hfp]; simp
    simp [h1, h2]
  -- integrability on the restricted product, for both Fubini swaps
  have hrestr : ∀ (g : (ℝ^(m+1)) × ℝ → ℝ), Continuous g → HasCompactSupport g →
      Integrable (Function.uncurry (fun (x : ℝ^(m+1)) (t : ℝ) => g (x, t))) (volume.prod (volume.restrict (Set.Iic (0:ℝ)))) := by
    intro g hg hgcs
    have hfull := hg.integrable_of_hasCompactSupport (μ := volume) hgcs
    rw [Measure.volume_eq_prod] at hfull
    have hmeq : (volume : Measure (ℝ^(m + 1))).prod (volume.restrict (Set.Iic (0:ℝ)))
        = ((volume : Measure (ℝ^(m + 1))).prod volume).restrict (Set.univ ×ˢ Set.Iic 0) := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]
    rw [hmeq]; exact hfull.restrict
  rw [MeasureTheory.integral_integral_swap (hrestr _ hdivcont hdivcs)]
  have hslice : ∀ t, ∫ x, divergence F (x, t) = ∫ x, fderiv ℝ (fun q => (F q).2) (x, t) (0, 1) := by
    intro t
    have hHint : ∀ i, Integrable
        (fun x : ℝ^(m + 1) => fderiv ℝ (fun q => (F q).1 i) (x, t) (EuclideanSpace.single i 1, 0)) := fun i =>
      ((hHcont i).comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport (μ := volume)
        (HasCompactSupport.intro ((hHcs i).image continuous_fst) (fun x hx =>
          image_eq_zero_of_notMem_tsupport
            (f := fun p => fderiv ℝ (fun q => (F q).1 i) p (EuclideanSpace.single i 1, 0))
            (fun hmem => hx ⟨(x, t), hmem, rfl⟩)))
    have hVint : Integrable
        (fun x : ℝ^(m + 1) => fderiv ℝ (fun q => (F q).2) (x, t) (0, 1)) :=
      (hVcont.comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport (μ := volume)
        (HasCompactSupport.intro (hVcs.image continuous_fst) (fun x hx =>
          image_eq_zero_of_notMem_tsupport
            (f := fun p => fderiv ℝ (fun q => (F q).2) p (0, 1))
            (fun hmem => hx ⟨(x, t), hmem, rfl⟩)))
    simp only [divergence]
    rw [integral_add (integrable_finset_sum _ (fun i _ => hHint i)) hVint,
      integral_finset_sum _ (fun i _ => hHint i)]
    simp_rw [integral_base_slice_deriv_eq_zero hF hsupp]
    simp
  simp_rw [hslice]
  rw [← MeasureTheory.integral_integral_swap (hrestr _ hVcont hVcs)]
  exact integral_Iic_vert_deriv_eq hF hsupp

/-- The product divergence of a `C¹` field is continuous. -/
theorem continuous_divergence {m : ℕ} {F : (ℝ^(m + 1)) × ℝ → (ℝ^(m + 1)) × ℝ} (hF : ContDiff ℝ 1 F) :
    Continuous (fun p => divergence F p) := by
  simp only [divergence]
  refine (continuous_finset_sum _ fun i _ => ?_).add
    ((((contDiff_snd.comp hF).continuous_fderiv (by norm_num)).clm_apply continuous_const))
  exact (((contDiff_piLp_apply 2).comp (contDiff_fst.comp hF)).continuous_fderiv (by norm_num)).clm_apply continuous_const

/-- The product divergence of a `C¹` compactly-supported field is compactly supported. -/
theorem hasCompactSupport_divergence {m : ℕ} {F : (ℝ^(m + 1)) × ℝ → (ℝ^(m + 1)) × ℝ}
    (hF : ContDiff ℝ 1 F) (hsupp : HasCompactSupport F) : HasCompactSupport (fun p => divergence F p) := by
  apply HasCompactSupport.intro (hsupp.fderiv (𝕜 := ℝ))
  intro p hp
  have hfp : fderiv ℝ F p = 0 := image_eq_zero_of_notMem_tsupport hp
  simp only [divergence]
  have h1 : ∀ i, fderiv ℝ (fun q => (F q).1 i) p (EuclideanSpace.single i 1, 0) = 0 := fun i => by
    have hclm : fderiv ℝ (fun q => (F q).1 i) p = ((EuclideanSpace.proj i).comp (ContinuousLinearMap.fst ℝ (ℝ^(m+1)) ℝ)).comp (fderiv ℝ F p) :=
      (((EuclideanSpace.proj i).comp (ContinuousLinearMap.fst ℝ (ℝ^(m+1)) ℝ)).hasFDerivAt.comp p (hF.differentiable (by norm_num) p).hasFDerivAt).fderiv
    rw [hclm, hfp]; simp
  have h2 : fderiv ℝ (fun q => (F q).2) p (0, 1) = 0 := by
    have hclm : fderiv ℝ (fun q => (F q).2) p = (ContinuousLinearMap.snd ℝ (ℝ^(m+1)) ℝ).comp (fderiv ℝ F p) :=
      ((ContinuousLinearMap.snd ℝ (ℝ^(m+1)) ℝ).hasFDerivAt.comp p (hF.differentiable (by norm_num) p).hasFDerivAt).fderiv
    rw [hclm, hfp]; simp
  simp [h1, h2]

/-- **The flat half-space slab.** Transfer of the product slab to flat coordinates. -/
theorem setIntegral_flatten_slab {m : ℕ} {F : (ℝ^(m + 1)) × ℝ → (ℝ^(m + 1)) × ℝ}
    (hF : ContDiff ℝ 1 F) (hsupp : HasCompactSupport F) :
    (∫ z in flatten m '' {p : WithLp 2 ((ℝ^(m + 1)) × ℝ) | (WithLp.ofLp p).2 ∈ Set.Iic (0:ℝ)},
        divergenceE (fun w => (flattenCLE m).symm (F (flattenCLE m w))) z)
      = ∫ x, (F (x, 0)).2 := by
  have hint : Integrable (Function.uncurry (fun (x : ℝ^(m+1)) (t : ℝ) => divergence F (x, t)))
      (volume.prod (volume.restrict (Set.Iic (0:ℝ)))) := by
    have hfull := (continuous_divergence hF).integrable_of_hasCompactSupport (μ := volume) (hasCompactSupport_divergence hF hsupp)
    rw [Measure.volume_eq_prod] at hfull
    have hmeq : (volume : Measure (ℝ^(m + 1))).prod (volume.restrict (Set.Iic (0:ℝ)))
        = ((volume : Measure (ℝ^(m + 1))).prod volume).restrict (Set.univ ×ˢ Set.Iic 0) := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]
    rw [hmeq]; exact hfull.restrict
  rw [setIntegral_flatten_image]
  simp_rw [divergenceE_flatten (hF.differentiable (by norm_num))]
  rw [setIntegral_ofLp]
  have hset : WithLp.ofLp '' {p : WithLp 2 ((ℝ^(m + 1)) × ℝ) | (WithLp.ofLp p).2 ∈ Set.Iic (0:ℝ)}
      = Set.univ ×ˢ Set.Iic (0:ℝ) := by
    ext q
    simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_prod, Set.mem_univ, true_and, Set.mem_Iic]
    constructor
    · rintro ⟨p, hp, rfl⟩; exact hp
    · intro hq; exact ⟨WithLp.toLp 2 q, hq, rfl⟩
  rw [hset]
  have hfub : ∫ q in Set.univ ×ˢ Set.Iic (0:ℝ), divergence F q ∂(volume : Measure ((ℝ^(m+1)) × ℝ))
      = ∫ x, ∫ t in Set.Iic (0:ℝ), divergence F (x, t) := by
    have hm : (volume : Measure ((ℝ^(m + 1)) × ℝ)).restrict (Set.univ ×ˢ Set.Iic (0:ℝ))
        = volume.prod (volume.restrict (Set.Iic 0)) := by
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
    rw [hm]; exact integral_prod _ hint
  rw [hfub]
  exact integral_Iic_divergence_eq hF hsupp

/-- Continuity of the canonical (flat) divergence of a `C¹` field. -/
theorem continuous_divergenceE {n : ℕ} {G : (ℝ^n) → (ℝ^n)} (hG : ContDiff ℝ 1 G) :
    Continuous (fun x => divergenceE G x) := by
  simp only [divergenceE]
  exact continuous_finset_sum _ fun i _ =>
    (EuclideanSpace.proj i).continuous.comp
      ((hG.continuous_fderiv (by norm_num)).clm_apply continuous_const)

/-- Compact support of the canonical divergence of a compactly-supported `C¹` field. -/
theorem hasCompactSupport_divergenceE {n : ℕ} {G : (ℝ^n) → (ℝ^n)}
    (_hG : ContDiff ℝ 1 G) (hGs : HasCompactSupport G) :
    HasCompactSupport (fun x => divergenceE G x) :=
  HasCompactSupport.intro (hGs.fderiv (𝕜 := ℝ)) (fun x hx => by
    simp only [divergenceE]
    rw [image_eq_zero_of_notMem_tsupport (f := fderiv ℝ G) hx]
    simp)

/-- Split of an `Iic` integral through `0`: `∫_{Iic b} g = ∫_{Iic 0} g + ∫₀^b g` (any sign of `b`),
the oriented additivity of the integral over the half-line. -/
theorem integral_Iic_split {g : ℝ → ℝ} (hg : Integrable g) (b : ℝ) :
    ∫ t in Set.Iic b, g t = (∫ t in Set.Iic (0 : ℝ), g t) + ∫ t in (0 : ℝ)..b, g t := by
  have h : (∫ t in Set.Iic b, g t) - (∫ t in Set.Iic (0 : ℝ), g t) = ∫ t in (0 : ℝ)..b, g t :=
    intervalIntegral.integral_Iic_sub_Iic (a := (0 : ℝ)) hg.integrableOn hg.integrableOn
  rw [← h]; ring

/-- Fubini over the region below a graph `{p.2 < γ p.1}` (no sign condition on `γ`). -/
theorem setIntegral_below {m : ℕ} {γ : (ℝ^m) → ℝ} (hγ : Measurable γ) {h : (ℝ^m) × ℝ → ℝ}
    (hint : IntegrableOn h {p : (ℝ^m) × ℝ | p.2 < γ p.1}) :
    ∫ p in {p : (ℝ^m) × ℝ | p.2 < γ p.1}, h p ∂(volume : Measure ((ℝ^m) × ℝ))
      = ∫ x, ∫ t in Set.Iio (γ x), h (x, t) := by
  have hmS : MeasurableSet {p : (ℝ^m) × ℝ | p.2 < γ p.1} :=
    measurableSet_lt measurable_snd (hγ.comp measurable_fst)
  have hint' : Integrable ({p : (ℝ^m) × ℝ | p.2 < γ p.1}.indicator h) :=
    (integrable_indicator_iff hmS).mpr hint
  rw [← integral_indicator hmS, Measure.volume_eq_prod,
    integral_prod _ (by rw [← Measure.volume_eq_prod]; exact hint')]
  refine integral_congr_ae (.of_forall fun x => ?_)
  have hfun : (fun t => {p : (ℝ^m) × ℝ | p.2 < γ p.1}.indicator h (x, t))
      = (Set.Iio (γ x)).indicator (fun t => h (x, t)) := by
    funext t
    by_cases htI : t ∈ Set.Iio (γ x)
    · rw [Set.indicator_of_mem htI,
        Set.indicator_of_mem (show (x, t) ∈ {p : (ℝ^m) × ℝ | p.2 < γ p.1} from htI)]
    · rw [Set.indicator_of_notMem htI,
        Set.indicator_of_notMem (show (x, t) ∉ {p : (ℝ^m) × ℝ | p.2 < γ p.1} from
          fun hmem => htI hmem)]
  change ∫ t, {p : (ℝ^m) × ℝ | p.2 < γ p.1}.indicator h (x, t) = ∫ t in Set.Iio (γ x), h (x, t)
  rw [hfun, integral_indicator measurableSet_Iio]

/-- Volume side of the bottomless (full-subgraph) divergence theorem, arbitrary `γ`: the flat
divergence over the full subgraph equals the iterated integral `∫ₓ ∫_{Iio(γx)} divergence F`. -/
theorem setIntegral_flatten_divergence_full {m : ℕ} {γ : (ℝ^(m + 1)) → ℝ} (hγ : ContDiff ℝ 1 γ)
    {F : (ℝ^(m + 1)) × ℝ → (ℝ^(m + 1)) × ℝ} (hF : ContDiff ℝ 1 F) (hsupp : HasCompactSupport F) :
    (∫ z in flatten m '' {p : WithLp 2 ((ℝ^(m + 1)) × ℝ) | (WithLp.ofLp p).2 < γ (WithLp.ofLp p).1},
        divergenceE (fun w => (flattenCLE m).symm (F (flattenCLE m w))) z)
      = ∫ x, ∫ t in Set.Iio (γ x), divergence F (x, t) := by
  have hcont : Continuous (fun p => divergence F p) := continuous_divergence hF
  have hcs : HasCompactSupport (fun p => divergence F p) := hasCompactSupport_divergence hF hsupp
  have hint : IntegrableOn (fun p => divergence F p) {p : (ℝ^(m + 1)) × ℝ | p.2 < γ p.1} :=
    (hcont.integrable_of_hasCompactSupport hcs).integrableOn
  rw [setIntegral_flatten_image]
  simp_rw [divergenceE_flatten (hF.differentiable (by norm_num))]
  rw [setIntegral_ofLp]
  have hset : WithLp.ofLp '' {p : WithLp 2 ((ℝ^(m + 1)) × ℝ) | (WithLp.ofLp p).2 < γ (WithLp.ofLp p).1}
      = {p : (ℝ^(m + 1)) × ℝ | p.2 < γ p.1} := by
    ext q
    simp only [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨p, hp, rfl⟩; exact hp
    · intro hq; exact ⟨WithLp.toLp 2 q, hq, rfl⟩
  rw [hset, setIntegral_below hγ.continuous.measurable hint]

/-- **Bottomless subgraph divergence theorem** (arbitrary `γ`, no sign condition): the flux of a
compactly-supported `C¹` field over the full strict subgraph `{height < γ}` equals the surface
integral over the graph. Proved via the iterated form `∫ₓ ∫_{Iic(γx)} = slab + graph` using the
oriented `Iic` split, so `γ` may take any sign. -/
theorem divergence_theorem_flat_bottomless {m : ℕ} {γ : (ℝ^(m + 1)) → ℝ} (hγ : ContDiff ℝ 1 γ)
    {F : (ℝ^(m + 1)) × ℝ → (ℝ^(m + 1)) × ℝ} (hF : ContDiff ℝ 1 F)
    (hsupp : HasCompactSupport F) :
    (∫ z in flatten m '' {p : WithLp 2 ((ℝ^(m + 1)) × ℝ) | (WithLp.ofLp p).2 < γ (WithLp.ofLp p).1},
        divergenceE (fun w => (flattenCLE m).symm (F (flattenCLE m w))) z)
      = ∫ z in flatten m '' (graphFun γ '' univ),
          (⟪(flattenCLE m).symm (F (flattenCLE m z)),
              flatten m (graphNormal γ ((flatten m).symm z).ofLp.1)⟫ : ℝ)
            ∂(μHE[m + 1] : Measure (ℝ^(m + 2))) := by
  have hgcont : Continuous (fun p => divergence F p) := continuous_divergence hF
  have hgcs : HasCompactSupport (fun p => divergence F p) := hasCompactSupport_divergence hF hsupp
  have hgint : ∀ x, Integrable (fun t => divergence F (x, t)) := fun x =>
    (hgcont.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.intro (hgcs.image continuous_snd) (fun t ht =>
        image_eq_zero_of_notMem_tsupport (f := fun p => divergence F p)
          (fun hmem => ht ⟨(x, t), hmem, rfl⟩)))
  have hsplit : ∀ x, ∫ t in Set.Iio (γ x), divergence F (x, t)
      = (∫ t in Set.Iic (0 : ℝ), divergence F (x, t)) + ∫ t in (0 : ℝ)..(γ x), divergence F (x, t) :=
    fun x => by
      rw [setIntegral_congr_set Iio_ae_eq_Iic, integral_Iic_split (hgint x) (γ x)]
  have hprodint : Integrable (Function.uncurry fun (x : ℝ^(m + 1)) (t : ℝ) => divergence F (x, t))
      (volume.prod (volume.restrict (Set.Iic (0 : ℝ)))) := by
    have hfull := hgcont.integrable_of_hasCompactSupport (μ := volume) hgcs
    rw [Measure.volume_eq_prod] at hfull
    have hmeq : (volume : Measure (ℝ^(m + 1))).prod (volume.restrict (Set.Iic (0 : ℝ)))
        = ((volume : Measure (ℝ^(m + 1))).prod volume).restrict (Set.univ ×ˢ Set.Iic 0) := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]
    rw [hmeq]; exact hfull.restrict
  have hInt1 : Integrable (fun x => ∫ t in Set.Iic (0 : ℝ), divergence F (x, t)) :=
    hprodint.integral_prod_left
  have hInt2 : Integrable (fun x => ∫ t in (0 : ℝ)..(γ x), divergence F (x, t)) := by
    refine (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hgcont
      hγ.continuous).integrable_of_hasCompactSupport ?_
    apply HasCompactSupport.intro (hgcs.image continuous_fst)
    intro x hx
    have hz : ∀ t, divergence F (x, t) = 0 := fun t =>
      image_eq_zero_of_notMem_tsupport (f := fun p => divergence F p)
        (fun hmem => hx ⟨(x, t), hmem, rfl⟩)
    simp [hz]
  rw [setIntegral_flatten_divergence_full hγ hF hsupp]
  simp_rw [hsplit]
  rw [integral_add hInt1 hInt2, integral_Iic_divergence_eq hF hsupp,
    divergence_theorem_graph hγ hF hsupp, ← setIntegral_flatten_flux]
  abel



/-- Translation invariance of the canonical divergence. -/
theorem divergenceE_comp_translation {n : ℕ} {F : (ℝ^n) → (ℝ^n)} (hF : Differentiable ℝ F)
    (c : ℝ^n) (x : ℝ^n) :
    divergenceE (fun y => F (y + c)) x = divergenceE F (x + c) := by
  simp only [divergenceE]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hfd : HasFDerivAt (fun y : ℝ^n => F (y + c)) (fderiv ℝ F (x + c)) x := by
    have h1 : HasFDerivAt (fun y : ℝ^n => y + c) (ContinuousLinearMap.id ℝ (ℝ^n)) x :=
      (hasFDerivAt_id x).add_const c
    simpa using (hF (x + c)).hasFDerivAt.comp x h1
  rw [hfd.fderiv]

/-- Divergence of the active transport of `V` by the affine rigid motion `x ↦ e (x - c)` equals the
divergence of `V`, transported: `div (e ∘ V ∘ (e⁻¹ · + c)) (e (x - c)) = div V x`. -/
theorem divergenceE_transport_affine {n : ℕ} (e : (ℝ^n) ≃ₗᵢ[ℝ] (ℝ^n)) (c : ℝ^n)
    {V : (ℝ^n) → (ℝ^n)} (hV : Differentiable ℝ V) (x : ℝ^n) :
    divergenceE (fun z => e (V (e.symm z + c))) (e (x - c)) = divergenceE V x := by
  have hH : Differentiable ℝ (fun y : ℝ^n => V (y + c)) := hV.comp (differentiable_id.add_const c)
  have h1 : divergenceE (fun z => e (V (e.symm z + c))) (e (x - c))
      = divergenceE (fun y => V (y + c)) (e.symm (e (x - c))) := by
    have hkey := divergenceE_comp_isometry e.symm (F := fun y => V (y + c)) hH (e (x - c))
    simpa using hkey
  rw [h1, e.symm_apply_apply, divergenceE_comp_translation hV c (x - c), sub_add_cancel]

/-- **General-field form of the bottomless subgraph divergence theorem.** For an arbitrary
compactly-supported `C¹` field `G` on `ℝᵐ⁺²`. -/
theorem divergence_theorem_flat_bottomless' {m : ℕ} {γ : (ℝ^(m + 1)) → ℝ} (hγ : ContDiff ℝ 1 γ)
    {G : (ℝ^(m + 2)) → (ℝ^(m + 2))} (hG : ContDiff ℝ 1 G)
    (hGsupp : HasCompactSupport G) :
    (∫ z in flatten m '' {p : WithLp 2 ((ℝ^(m + 1)) × ℝ) | (WithLp.ofLp p).2 < γ (WithLp.ofLp p).1},
        divergenceE G z)
      = ∫ z in flatten m '' (graphFun γ '' univ),
          (⟪G z, flatten m (graphNormal γ ((flatten m).symm z).ofLp.1)⟫ : ℝ)
            ∂(μHE[m + 1] : Measure (ℝ^(m + 2))) := by
  have hFcd : ContDiff ℝ 1 (fun q => flattenCLE m (G ((flattenCLE m).symm q))) :=
    (flattenCLE m).contDiff.comp (hG.comp (flattenCLE m).symm.contDiff)
  have hFcs : HasCompactSupport (fun q => flattenCLE m (G ((flattenCLE m).symm q))) :=
    (hGsupp.comp_isClosedEmbedding (flattenCLE m).symm.toHomeomorph.isClosedEmbedding).comp_left
      (g := ⇑(flattenCLE m)) (map_zero _)
  have key := divergence_theorem_flat_bottomless hγ
    (F := fun q => flattenCLE m (G ((flattenCLE m).symm q))) hFcd hFcs
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using key

/-- Change of variables for a volume integral under the affine rigid motion `x ↦ e (x - c)`. -/
theorem setIntegral_rigid_image {n : ℕ} (e : (ℝ^n) ≃ₗᵢ[ℝ] (ℝ^n)) (c : ℝ^n)
    (g : (ℝ^n) → ℝ) (s : Set (ℝ^n)) :
    ∫ z in (fun x => e (x - c)) '' s, g z = ∫ x in s, g (e (x - c)) := by
  have hmp : MeasurePreserving (fun x : ℝ^n => e (x - c)) :=
    (LinearIsometryEquiv.measurePreserving e).comp (measurePreserving_sub_right volume c)
  have hemb : MeasurableEmbedding (fun x : ℝ^n => e (x - c)) :=
    e.toHomeomorph.measurableEmbedding.comp (measurableEmbedding_subRight c)
  rw [← hmp.setIntegral_preimage_emb hemb g ((fun x => e (x - c)) '' s),
    Set.preimage_image_eq s hemb.injective]

/-- The affine rigid motion `x ↦ e (x - c)` preserves the `(m+1)`-dim surface measure `μHE`. -/
theorem measurePreserving_rigid_μHE {m : ℕ} (e : (ℝ^(m + 2)) ≃ₗᵢ[ℝ] (ℝ^(m + 2))) (c : ℝ^(m + 2)) :
    MeasurePreserving (fun x : ℝ^(m + 2) => e (x - c))
      (μHE[m + 1] : Measure (ℝ^(m + 2))) (μHE[m + 1] : Measure (ℝ^(m + 2))) := by
  have hiso : Isometry (fun x : ℝ^(m + 2) => e (x - c)) :=
    e.isometry.comp (IsometryEquiv.subRight c).isometry
  have hsurj : Function.Surjective (fun x : ℝ^(m + 2) => e (x - c)) :=
    fun y => ⟨e.symm y + c, by simp⟩
  refine ⟨hiso.continuous.measurable, ?_⟩
  ext t ht
  rw [Measure.map_apply hiso.continuous.measurable ht,
    ← hiso.euclideanHausdorffMeasure_image ((fun x => e (x - c)) ⁻¹' t),
    Set.image_preimage_eq t hsurj]

/-- Change of variables for a `μHE` surface integral under the affine rigid motion `x ↦ e (x - c)`. -/
theorem setIntegral_rigid_image_μHE {m : ℕ} (e : (ℝ^(m + 2)) ≃ₗᵢ[ℝ] (ℝ^(m + 2))) (c : ℝ^(m + 2))
    (g : (ℝ^(m + 2)) → ℝ) (s : Set (ℝ^(m + 2))) :
    ∫ z in (fun x => e (x - c)) '' s, g z ∂(μHE[m + 1] : Measure (ℝ^(m + 2)))
      = ∫ x in s, g (e (x - c)) ∂(μHE[m + 1] : Measure (ℝ^(m + 2))) := by
  have hemb : MeasurableEmbedding (fun x : ℝ^(m + 2) => e (x - c)) :=
    e.toHomeomorph.measurableEmbedding.comp (measurableEmbedding_subRight c)
  rw [← (measurePreserving_rigid_μHE e c).setIntegral_preimage_emb hemb g
      ((fun x => e (x - c)) '' s),
    Set.preimage_image_eq s hemb.injective]

/-- The physical subgraph (in the chart frame) is the rigid image of the flat subgraph. -/
theorem rigid_image_subgraph {m : ℕ} (e : (ℝ^(m + 2)) ≃ₗᵢ[ℝ] (ℝ^(m + 2))) (c : ℝ^(m + 2))
    (γ : (ℝ^(m + 1)) → ℝ) :
    (fun x : ℝ^(m + 2) => e (x - c)) ''
        {x | ((flatten m).symm (e (x - c))).ofLp.2 < γ ((flatten m).symm (e (x - c))).ofLp.1}
      = flatten m '' {p : WithLp 2 ((ℝ^(m + 1)) × ℝ) | (WithLp.ofLp p).2 < γ (WithLp.ofLp p).1} := by
  have hsurj : Function.Surjective (fun x : ℝ^(m + 2) => e (x - c)) :=
    fun y => ⟨e.symm y + c, by simp⟩
  have hS : {x : ℝ^(m + 2) |
        ((flatten m).symm (e (x - c))).ofLp.2 < γ ((flatten m).symm (e (x - c))).ofLp.1}
      = (fun x => e (x - c)) ⁻¹'
          (flatten m '' {p : WithLp 2 ((ℝ^(m + 1)) × ℝ) | (WithLp.ofLp p).2 < γ (WithLp.ofLp p).1}) := by
    rw [LinearIsometryEquiv.image_eq_preimage_symm]; rfl
  rw [hS, Set.image_preimage_eq _ hsurj]

/-- **Chart flux (milestone 3b): the single-chart divergence theorem.** For a compactly-supported
`C¹` field `V` and a chart with rotation `e` about center `c` in which `Ω` is the subgraph
`{height < γ}`, the volume integral of `div V` over the physical subgraph equals the flux over the
physical graph, with outward normal `ν x = e⁻¹ (flatten (graphNormal γ (base))). -/
theorem chart_flux {m : ℕ} (e : (ℝ^(m + 2)) ≃ₗᵢ[ℝ] (ℝ^(m + 2))) (c : ℝ^(m + 2))
    {γ : (ℝ^(m + 1)) → ℝ} (hγ : ContDiff ℝ 1 γ)
    {V : (ℝ^(m + 2)) → (ℝ^(m + 2))} (hV : ContDiff ℝ 1 V) (hVsupp : HasCompactSupport V) :
    (∫ x in {x | ((flatten m).symm (e (x - c))).ofLp.2 < γ ((flatten m).symm (e (x - c))).ofLp.1},
        divergenceE V x)
      = ∫ x in (fun x => e (x - c)) ⁻¹' (flatten m '' (graphFun γ '' univ)),
          (⟪V x, e.symm (flatten m (graphNormal γ ((flatten m).symm (e (x - c))).ofLp.1))⟫ : ℝ)
            ∂(μHE[m + 1] : Measure (ℝ^(m + 2))) := by
  set G : (ℝ^(m + 2)) → (ℝ^(m + 2)) := fun z => e (V (e.symm z + c)) with hG
  have hshift : Topology.IsClosedEmbedding (fun z : ℝ^(m + 2) => e.symm z + c) :=
    (Homeomorph.addRight c).isClosedEmbedding.comp e.symm.toHomeomorph.isClosedEmbedding
  have hGcd : ContDiff ℝ 1 G :=
    e.toContinuousLinearEquiv.contDiff.comp
      (hV.comp (e.symm.toContinuousLinearEquiv.contDiff.add contDiff_const))
  have hGcs : HasCompactSupport G :=
    (hVsupp.comp_isClosedEmbedding hshift).comp_left (g := ⇑e) (map_zero _)
  -- volume side: physical subgraph integral = flat subgraph integral
  have hvol : (∫ x in {x | ((flatten m).symm (e (x - c))).ofLp.2 < γ ((flatten m).symm (e (x - c))).ofLp.1},
        divergenceE V x)
      = ∫ z in flatten m '' {p : WithLp 2 ((ℝ^(m + 1)) × ℝ) | (WithLp.ofLp p).2 < γ (WithLp.ofLp p).1},
        divergenceE G z := by
    rw [← rigid_image_subgraph e c γ, setIntegral_rigid_image e c (fun z => divergenceE G z) _]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x =>
      (divergenceE_transport_affine e c (hV.differentiable (by norm_num)) x).symm)
  -- flux side: flat graph flux = physical graph flux
  have hflux : (∫ z in flatten m '' (graphFun γ '' univ),
        (⟪G z, flatten m (graphNormal γ ((flatten m).symm z).ofLp.1)⟫ : ℝ)
          ∂(μHE[m + 1] : Measure (ℝ^(m + 2))))
      = ∫ x in (fun x => e (x - c)) ⁻¹' (flatten m '' (graphFun γ '' univ)),
          (⟪V x, e.symm (flatten m (graphNormal γ ((flatten m).symm (e (x - c))).ofLp.1))⟫ : ℝ)
            ∂(μHE[m + 1] : Measure (ℝ^(m + 2))) := by
    have hsurj : Function.Surjective (fun x : ℝ^(m + 2) => e (x - c)) :=
      fun y => ⟨e.symm y + c, by simp⟩
    have himg : flatten m '' (graphFun γ '' univ)
        = (fun x => e (x - c)) '' ((fun x => e (x - c)) ⁻¹' (flatten m '' (graphFun γ '' univ))) :=
      (Set.image_preimage_eq _ hsurj).symm
    calc (∫ z in flatten m '' (graphFun γ '' univ),
            (⟪G z, flatten m (graphNormal γ ((flatten m).symm z).ofLp.1)⟫ : ℝ)
              ∂(μHE[m + 1] : Measure (ℝ^(m + 2))))
        = ∫ z in (fun x => e (x - c)) '' ((fun x => e (x - c)) ⁻¹' (flatten m '' (graphFun γ '' univ))),
            (⟪G z, flatten m (graphNormal γ ((flatten m).symm z).ofLp.1)⟫ : ℝ)
              ∂(μHE[m + 1] : Measure (ℝ^(m + 2))) := by rw [← himg]
      _ = ∫ x in (fun x => e (x - c)) ⁻¹' (flatten m '' (graphFun γ '' univ)),
            (⟪G (e (x - c)),
                flatten m (graphNormal γ ((flatten m).symm (e (x - c))).ofLp.1)⟫ : ℝ)
              ∂(μHE[m + 1] : Measure (ℝ^(m + 2))) :=
          setIntegral_rigid_image_μHE e c
            (fun z => (⟪G z, flatten m (graphNormal γ ((flatten m).symm z).ofLp.1)⟫ : ℝ)) _
      _ = ∫ x in (fun x => e (x - c)) ⁻¹' (flatten m '' (graphFun γ '' univ)),
            (⟪V x, e.symm (flatten m (graphNormal γ ((flatten m).symm (e (x - c))).ofLp.1))⟫ : ℝ)
              ∂(μHE[m + 1] : Measure (ℝ^(m + 2))) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          have hGAx : G (e (x - c)) = e (V x) := by
            simp only [hG, e.symm_apply_apply, sub_add_cancel]
          have hinner := e.inner_map_map (V x)
            (e.symm (flatten m (graphNormal γ ((flatten m).symm (e (x - c))).ofLp.1)))
          rw [e.apply_symm_apply] at hinner
          show (⟪G (e (x - c)),
              flatten m (graphNormal γ ((flatten m).symm (e (x - c))).ofLp.1)⟫ : ℝ)
            = ⟪V x, e.symm (flatten m (graphNormal γ ((flatten m).symm (e (x - c))).ofLp.1))⟫
          rw [hGAx]; exact hinner
  rw [hvol, divergence_theorem_flat_bottomless' hγ hGcd hGcs]
  exact hflux


/-- In the product `ℝᵐ⁺¹ × ℝ`, the frontier of the open subgraph `{q.2 < γ q.1}` is the graph
`{q.2 = γ q.1}` — the height coordinate is free, so every graph point is a limit of subgraph points. -/
theorem frontier_subgraph_prod {m : ℕ} {γ : (ℝ^(m + 1)) → ℝ} (hγ : Continuous γ) :
    frontier {q : (ℝ^(m + 1)) × ℝ | q.2 < γ q.1} = {q | q.2 = γ q.1} := by
  apply Set.Subset.antisymm
  · exact frontier_lt_subset_eq continuous_snd (hγ.comp continuous_fst)
  · intro q hq
    rw [Set.mem_setOf_eq] at hq
    rw [frontier_eq_closure_inter_closure]
    refine ⟨?_, ?_⟩
    · refine mem_closure_iff_seq_limit.mpr
        ⟨fun n => (q.1, γ q.1 - 1 / ((n : ℝ) + 1)), fun n => ?_, ?_⟩
      · have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by
          have hn : (0 : ℝ) < (n : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
          exact div_pos one_pos hn
        show γ q.1 - 1 / ((n : ℝ) + 1) < γ q.1
        linarith
      · have h0 : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        have h2 : Filter.Tendsto (fun n : ℕ => γ q.1 - 1 / ((n : ℝ) + 1)) Filter.atTop
            (nhds (γ q.1)) := by
          simpa using (tendsto_const_nhds (x := γ q.1)).sub h0
        have hlim : Filter.Tendsto
            (fun n : ℕ => ((q.1, γ q.1 - 1 / ((n : ℝ) + 1)) : (ℝ^(m + 1)) × ℝ))
            Filter.atTop (nhds (q.1, γ q.1)) := tendsto_const_nhds.prodMk_nhds h2
        have hqeq : ((q.1, γ q.1) : (ℝ^(m + 1)) × ℝ) = q := by rw [← hq]
        rwa [hqeq] at hlim
    · apply subset_closure
      rw [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt, hq]

/-- **Chart boundary is the graph.** In a boundary chart with rotation `e` about `c`, the frontier
of the physical subgraph `{height < γ}` is the physical graph `{height = γ}`. -/
theorem chart_frontier {m : ℕ} (e : (ℝ^(m + 2)) ≃ₗᵢ[ℝ] (ℝ^(m + 2))) (c : ℝ^(m + 2))
    {γ : (ℝ^(m + 1)) → ℝ} (hγ : Continuous γ) :
    frontier {x | ((flatten m).symm (e (x - c))).ofLp.2 < γ ((flatten m).symm (e (x - c))).ofLp.1}
      = {x | ((flatten m).symm (e (x - c))).ofLp.2 = γ ((flatten m).symm (e (x - c))).ofLp.1} := by
  let R : (ℝ^(m + 2)) ≃ₜ (ℝ^(m + 2)) :=
    { toFun := fun x => e (x - c), invFun := fun z => e.symm z + c,
      left_inv := fun x => by simp, right_inv := fun z => by simp,
      continuous_toFun := e.continuous.comp (continuous_id.sub continuous_const),
      continuous_invFun := e.symm.continuous.add continuous_const }
  let Φ : (ℝ^(m + 2)) ≃ₜ ((ℝ^(m + 1)) × ℝ) :=
    (R.trans (flatten m).symm.toHomeomorph).trans (WithLp.homeomorphProd 2 (ℝ^(m + 1)) ℝ)
  have hsub : {x | ((flatten m).symm (e (x - c))).ofLp.2 < γ ((flatten m).symm (e (x - c))).ofLp.1}
      = Φ ⁻¹' {q : (ℝ^(m + 1)) × ℝ | q.2 < γ q.1} := rfl
  have hgr : {x | ((flatten m).symm (e (x - c))).ofLp.2 = γ ((flatten m).symm (e (x - c))).ofLp.1}
      = Φ ⁻¹' {q : (ℝ^(m + 1)) × ℝ | q.2 = γ q.1} := rfl
  rw [hsub, hgr, ← Homeomorph.preimage_frontier, frontier_subgraph_prod hγ]

/-- **Frontier is local on an open set.** If `s` and `t` agree on an open `U`, their frontiers
agree on `U`. -/
theorem frontier_inter_open_eq {X : Type*} [TopologicalSpace X] {s t U : Set X} (hU : IsOpen U)
    (h : s ∩ U = t ∩ U) : frontier s ∩ U = frontier t ∩ U := by
  have sub : ∀ a b : Set X, a ∩ U = b ∩ U → closure a ∩ U ⊆ closure b := by
    rintro a b hab x ⟨hxc, hxU⟩
    rw [_root_.mem_closure_iff]
    intro o ho hxo
    obtain ⟨y, hyoU, hya⟩ := _root_.mem_closure_iff.mp hxc (o ∩ U) (ho.inter hU) ⟨hxo, hxU⟩
    exact ⟨y, hyoU.1, (hab ▸ Set.mem_inter hya hyoU.2 : y ∈ b ∩ U).1⟩
  have cl : ∀ a b : Set X, a ∩ U = b ∩ U → closure a ∩ U = closure b ∩ U := fun a b hab =>
    Set.Subset.antisymm (fun x hx => ⟨sub a b hab hx, hx.2⟩) (fun x hx => ⟨sub b a hab.symm hx, hx.2⟩)
  have hc : sᶜ ∩ U = tᶜ ∩ U := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_compl_iff]
    constructor
    · rintro ⟨hxs, hxU⟩
      exact ⟨fun hxt => hxs (h.symm ▸ Set.mem_inter hxt hxU : x ∈ s ∩ U).1, hxU⟩
    · rintro ⟨hxt, hxU⟩
      exact ⟨fun hxs => hxt (h ▸ Set.mem_inter hxs hxU : x ∈ t ∩ U).1, hxU⟩
  rw [frontier_eq_closure_inter_closure, frontier_eq_closure_inter_closure,
    show closure s ∩ closure sᶜ ∩ U = (closure s ∩ U) ∩ (closure sᶜ ∩ U) from by ext x; simp; tauto,
    cl s t h, cl sᶜ tᶜ hc,
    show (closure t ∩ U) ∩ (closure tᶜ ∩ U) = closure t ∩ closure tᶜ ∩ U from by ext x; simp; tauto]

/-- **The boundary of the domain is the chart graph.** In a boundary chart, `frontier Ω ∩ ball`
equals the physical graph `{height = γ}` intersected with the ball. -/
theorem chart_frontier_domain {m : ℕ} (e : (ℝ^(m + 2)) ≃ₗᵢ[ℝ] (ℝ^(m + 2))) (c : ℝ^(m + 2))
    {γ : (ℝ^(m + 1)) → ℝ} (hγ : Continuous γ) {Ω : Set (ℝ^(m + 2))} {r : ℝ}
    (hchart : Ω ∩ Metric.ball c r
      = {x | ((flatten m).symm (e (x - c))).ofLp.2 < γ ((flatten m).symm (e (x - c))).ofLp.1}
        ∩ Metric.ball c r) :
    frontier Ω ∩ Metric.ball c r
      = {x | ((flatten m).symm (e (x - c))).ofLp.2 = γ ((flatten m).symm (e (x - c))).ofLp.1}
        ∩ Metric.ball c r := by
  rw [frontier_inter_open_eq Metric.isOpen_ball hchart, chart_frontier e c hγ]


/-- If `f` is supported in `B` and `s`, `t` agree on `B`, then `∫_s f = ∫_t f`. -/
theorem setIntegral_eq_of_support_subset {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure X} {s t B : Set X} {f : X → E}
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hf : Function.support f ⊆ B)
    (hst : s ∩ B = t ∩ B) :
    ∫ x in s, f x ∂μ = ∫ x in t, f x ∂μ := by
  classical
  rw [← integral_indicator hs, ← integral_indicator ht]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  by_cases hxB : x ∈ B
  · by_cases hxs : x ∈ s
    · have hxt : x ∈ t := (hst ▸ Set.mem_inter hxs hxB : x ∈ t ∩ B).1
      rw [Set.indicator_of_mem hxs, Set.indicator_of_mem hxt]
    · have hxt : x ∉ t := fun hh => hxs (hst.symm ▸ Set.mem_inter hh hxB : x ∈ s ∩ B).1
      rw [Set.indicator_of_notMem hxs, Set.indicator_of_notMem hxt]
  · have hfx : f x = 0 := by by_contra hh; exact hxB (hf (Function.mem_support.mpr hh))
    rw [Set.indicator_apply, Set.indicator_apply, hfx]; simp

/-- The physical graph (preimage of the flat graph under the chart rigid motion) is the level set
`{height = γ(base)}`. -/
theorem physical_graph_eq {m : ℕ} (e : (ℝ^(m + 2)) ≃ₗᵢ[ℝ] (ℝ^(m + 2))) (c : ℝ^(m + 2))
    (γ : (ℝ^(m + 1)) → ℝ) :
    (fun x => e (x - c)) ⁻¹' (flatten m '' (graphFun γ '' univ))
      = {x | ((flatten m).symm (e (x - c))).ofLp.2 = γ ((flatten m).symm (e (x - c))).ofLp.1} := by
  have hofLp : ∀ y : ℝ^(m + 1), (graphFun γ y).ofLp = (y, γ y) := fun y => rfl
  ext x
  simp only [Set.mem_preimage, Set.mem_image, Set.mem_setOf_eq, Set.mem_univ, true_and]
  constructor
  · rintro ⟨p, ⟨y, rfl⟩, hpe⟩
    have hpsy : (flatten m).symm (e (x - c)) = graphFun γ y := by
      rw [← hpe, LinearIsometryEquiv.symm_apply_apply]
    rw [hpsy, hofLp]
  · intro hx
    refine ⟨graphFun γ ((flatten m).symm (e (x - c))).ofLp.1, ⟨_, rfl⟩, ?_⟩
    have hg : graphFun γ ((flatten m).symm (e (x - c))).ofLp.1 = (flatten m).symm (e (x - c)) := by
      apply WithLp.ofLp_injective
      rw [hofLp]
      exact Prod.ext rfl hx.symm
    rw [hg, LinearIsometryEquiv.apply_symm_apply]

/-- **Chart term of the assembly.** For a field `V` supported inside a boundary chart ball, the
single-chart divergence theorem in the domain `Ω`: `∫_Ω divergenceE V = ∫_{∂Ω} ⟪V, ν⟫ dμHE`. -/
theorem chart_term {m : ℕ} (e : (ℝ^(m + 2)) ≃ₗᵢ[ℝ] (ℝ^(m + 2))) (c : ℝ^(m + 2))
    {γ : (ℝ^(m + 1)) → ℝ} (hγ : ContDiff ℝ 1 γ)
    {Ω : Set (ℝ^(m + 2))} (hΩ : MeasurableSet Ω) {r : ℝ}
    (hchart : Ω ∩ Metric.ball c r
      = {x | ((flatten m).symm (e (x - c))).ofLp.2 < γ ((flatten m).symm (e (x - c))).ofLp.1}
        ∩ Metric.ball c r)
    {ν : (ℝ^(m + 2)) → (ℝ^(m + 2))}
    (hν : ∀ x ∈ frontier Ω ∩ Metric.ball c r,
      ν x = e.symm (flatten m (graphNormal γ ((flatten m).symm (e (x - c))).ofLp.1)))
    {V : (ℝ^(m + 2)) → (ℝ^(m + 2))} (hV : ContDiff ℝ 1 V) (hVsupp : HasCompactSupport V)
    (hVball : tsupport V ⊆ Metric.ball c r) :
    ∫ x in Ω, divergenceE V x
      = ∫ x in frontier Ω, (⟪V x, ν x⟫ : ℝ) ∂(μHE[m + 1] : Measure (ℝ^(m + 2))) := by
  have hψ : Continuous (fun x : ℝ^(m + 2) => (flatten m).symm (e (x - c))) :=
    (flatten m).symm.continuous.comp (e.continuous.comp (continuous_id.sub continuous_const))
  have hofLpc : Continuous (WithLp.ofLp : WithLp 2 ((ℝ^(m + 1)) × ℝ) → (ℝ^(m + 1)) × ℝ) :=
    (WithLp.homeomorphProd 2 (ℝ^(m + 1)) ℝ).continuous
  have hheight : Continuous (fun x : ℝ^(m + 2) => ((flatten m).symm (e (x - c))).ofLp.2) :=
    continuous_snd.comp (hofLpc.comp hψ)
  have hgbase : Continuous (fun x : ℝ^(m + 2) => γ ((flatten m).symm (e (x - c))).ofLp.1) :=
    hγ.continuous.comp (continuous_fst.comp (hofLpc.comp hψ))
  have hsubmeas : MeasurableSet {x : ℝ^(m + 2) |
      ((flatten m).symm (e (x - c))).ofLp.2 < γ ((flatten m).symm (e (x - c))).ofLp.1} :=
    measurableSet_lt hheight.measurable hgbase.measurable
  have hgraphmeas : MeasurableSet {x : ℝ^(m + 2) |
      ((flatten m).symm (e (x - c))).ofLp.2 = γ ((flatten m).symm (e (x - c))).ofLp.1} :=
    (isClosed_eq hheight hgbase).measurableSet
  have hfrontmeas : MeasurableSet (frontier Ω) := isClosed_frontier.measurableSet
  have hVsub : Function.support V ⊆ Metric.ball c r := subset_trans (subset_tsupport V) hVball
  have hdivsup : Function.support (fun x => divergenceE V x) ⊆ Metric.ball c r := by
    refine subset_trans (fun x hx => ?_) hVball
    by_contra hxts
    have hV0 : V =ᶠ[nhds x] 0 := notMem_tsupport_iff_eventuallyEq.mp hxts
    have hfd : fderiv ℝ V x = 0 := by rw [hV0.fderiv_eq]; simp
    exact hx (by simp [divergenceE, hfd])
  have hVsupI : Function.support (fun x => (⟪V x,
      e.symm (flatten m (graphNormal γ ((flatten m).symm (e (x - c))).ofLp.1))⟫ : ℝ))
      ⊆ Metric.ball c r := by
    refine subset_trans (fun x hx => ?_) hVsub
    simp only [Function.mem_support, ne_eq] at hx ⊢
    exact fun h => hx (by rw [h, inner_zero_left])
  have hvol : ∫ x in Ω, divergenceE V x
      = ∫ x in {x | ((flatten m).symm (e (x - c))).ofLp.2 < γ ((flatten m).symm (e (x - c))).ofLp.1},
        divergenceE V x :=
    setIntegral_eq_of_support_subset hΩ hsubmeas hdivsup hchart
  have hflux := chart_flux e c hγ hV hVsupp
  rw [physical_graph_eq e c γ] at hflux
  rw [hvol, hflux,
    setIntegral_eq_of_support_subset hgraphmeas hfrontmeas hVsupI
      (chart_frontier_domain e c hγ.continuous hchart).symm]
  refine setIntegral_congr_fun hfrontmeas (fun x hx => ?_)
  by_cases hxball : x ∈ Metric.ball c r
  · rw [hν x ⟨hx, hxball⟩]
  · have hV0 : V x = 0 := image_eq_zero_of_notMem_tsupport (fun hmem => hxball (hVball hmem))
    simp [hV0]


/-- The surface measure of one boundary chart's graph piece is finite. -/
theorem surfaceMeasure_graphSet_lt_top {m : ℕ} (e : (ℝ^(m + 2)) ≃ₗᵢ[ℝ] (ℝ^(m + 2)))
    (c : ℝ^(m + 2)) {γ : (ℝ^(m + 1)) → ℝ} (hγ : ContDiff ℝ 1 γ) (r : ℝ) :
    (μHE[m + 1] : Measure (ℝ^(m + 2)))
        ({x | ((flatten m).symm (e (x - c))).ofLp.2 = γ ((flatten m).symm (e (x - c))).ofLp.1}
          ∩ Metric.ball c r) < ⊤ := by
  have hofLp : ∀ y : ℝ^(m + 1), (graphFun γ y).ofLp = (y, γ y) := fun y => rfl
  have hgfcont : Continuous (graphFun γ) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ (ℝ^(m + 1)) ℝ).symm.continuous.comp
      (continuous_id.prodMk hγ.continuous)
  have hmeasSet : MeasurableSet
      (flatten m '' (graphFun γ '' Metric.closedBall (0 : ℝ^(m + 1)) r)) :=
    (flatten m).toHomeomorph.measurableEmbedding.measurableSet_image.mpr
      ((isCompact_closedBall _ _).image hgfcont).isClosed.measurableSet
  have hsubset : {x : ℝ^(m + 2) |
        ((flatten m).symm (e (x - c))).ofLp.2 = γ ((flatten m).symm (e (x - c))).ofLp.1}
        ∩ Metric.ball c r
      ⊆ (fun x => e (x - c)) ⁻¹'
          (flatten m '' (graphFun γ '' Metric.closedBall (0 : ℝ^(m + 1)) r)) := by
    rintro x ⟨hxg, hxb⟩
    have hbase : ‖((flatten m).symm (e (x - c))).ofLp.1‖ ≤ r := by
      calc ‖((flatten m).symm (e (x - c))).ofLp.1‖
          ≤ ‖(flatten m).symm (e (x - c))‖ := ((flatten m).symm (e (x - c))).norm_fst_le
        _ = ‖e (x - c)‖ := (flatten m).symm.norm_map _
        _ = ‖x - c‖ := e.norm_map _
        _ ≤ r := by rw [← dist_eq_norm]; exact le_of_lt (Metric.mem_ball.mp hxb)
    have hgf : (flatten m).symm (e (x - c)) = graphFun γ ((flatten m).symm (e (x - c))).ofLp.1 := by
      apply WithLp.ofLp_injective 2
      rw [hofLp]
      exact Prod.ext rfl hxg
    refine ⟨graphFun γ ((flatten m).symm (e (x - c))).ofLp.1,
      ⟨_, Metric.mem_closedBall.mpr (by rw [dist_zero_right]; exact hbase), rfl⟩, ?_⟩
    rw [← hgf, LinearIsometryEquiv.apply_symm_apply]
  calc (μHE[m + 1] : Measure (ℝ^(m + 2)))
        ({x | ((flatten m).symm (e (x - c))).ofLp.2 = γ ((flatten m).symm (e (x - c))).ofLp.1}
          ∩ Metric.ball c r)
      ≤ μHE[m + 1] ((fun x => e (x - c)) ⁻¹'
          (flatten m '' (graphFun γ '' Metric.closedBall (0 : ℝ^(m + 1)) r))) := measure_mono hsubset
    _ = μHE[m + 1] (flatten m '' (graphFun γ '' Metric.closedBall (0 : ℝ^(m + 1)) r)) :=
        (measurePreserving_rigid_μHE e c).measure_preimage hmeasSet.nullMeasurableSet
    _ = μHE[m + 1] (graphFun γ '' Metric.closedBall (0 : ℝ^(m + 1)) r) :=
        (flatten m).isometry.euclideanHausdorffMeasure_image _
    _ = ∫⁻ x in Metric.closedBall (0 : ℝ^(m + 1)) r,
          ENNReal.ofReal (Real.sqrt (1 + ‖gradient γ x‖ ^ 2)) ∂volume :=
        area_formula_graph hγ measurableSet_closedBall
    _ < ⊤ := by
        obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℝ^(m + 1)) r).exists_bound_of_continuousOn
          (continuous_graph_integrand hγ).continuousOn
        calc ∫⁻ x in Metric.closedBall (0 : ℝ^(m + 1)) r,
                ENNReal.ofReal (Real.sqrt (1 + ‖gradient γ x‖ ^ 2)) ∂volume
            ≤ ∫⁻ _ in Metric.closedBall (0 : ℝ^(m + 1)) r, ENNReal.ofReal C ∂volume := by
              refine setLIntegral_mono measurable_const (fun x hx => ENNReal.ofReal_le_ofReal ?_)
              exact le_trans (le_abs_self _) (by rw [← Real.norm_eq_abs]; exact hC x hx)
          _ = ENNReal.ofReal C * volume (Metric.closedBall (0 : ℝ^(m + 1)) r) := setLIntegral_const _ _
          _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top

/-- The surface measure of the boundary of a bounded `C¹` domain is finite. -/
theorem surfaceMeasure_frontier_lt_top {m : ℕ} {Ω : Set (ℝ^(m + 2))} (hΩ : IsBoundedC1Domain Ω) :
    (μHE[m + 1] : Measure (ℝ^(m + 2))) (frontier Ω) < ⊤ := by
  obtain ⟨ι, _fin, c, r, hr, hcov, hcharts⟩ := hΩ.exists_finite_chart_cover
  have hcover : frontier Ω = ⋃ j, frontier Ω ∩ Metric.ball (c j) (r j) := by
    rw [← Set.inter_iUnion]; exact (Set.inter_eq_left.mpr hcov).symm
  rw [hcover]
  refine lt_of_le_of_lt (measure_iUnion_le _) ?_
  rw [tsum_fintype]
  refine ENNReal.sum_lt_top.mpr (fun j _ => ?_)
  obtain ⟨e, γ, hγ, hchart⟩ := hcharts j
  rw [chart_frontier_domain e (c j) hγ.continuous hchart]
  exact surfaceMeasure_graphSet_lt_top e (c j) hγ (r j)

/-- An **outward unit normal** for a bounded `C¹` domain `Ω`: a continuous field `ν` that, in every
subgraph chart (rotation `e` about `c` in which `Ω` is `{height < γ}`), agrees on the boundary with
the transported upward graph normal `e⁻¹ (flatten (graphNormal γ (base)))`. -/
structure IsOutwardNormal {m : ℕ} (Ω : Set (ℝ^(m + 2))) (ν : (ℝ^(m + 2)) → (ℝ^(m + 2))) : Prop where
  continuous : Continuous ν
  eq_chart : ∀ (c : ℝ^(m + 2)) (r : ℝ) (e : (ℝ^(m + 2)) ≃ₗᵢ[ℝ] (ℝ^(m + 2))) (γ : (ℝ^(m + 1)) → ℝ),
    ContDiff ℝ 1 γ →
    Ω ∩ Metric.ball c r
      = {x | ((flatten m).symm (e (x - c))).ofLp.2 < γ ((flatten m).symm (e (x - c))).ofLp.1}
        ∩ Metric.ball c r →
    ∀ x ∈ frontier Ω ∩ Metric.ball c r,
      ν x = e.symm (flatten m (graphNormal γ ((flatten m).symm (e (x - c))).ofLp.1))

/-- **The general divergence theorem (Gauss–Green) on a bounded `C¹` domain.** -/
theorem divergence_theorem {m : ℕ} {Ω : Set (ℝ^(m + 2))} (hΩ : IsBoundedC1Domain Ω)
    {ν : (ℝ^(m + 2)) → (ℝ^(m + 2))} (hν : IsOutwardNormal Ω ν)
    {F : (ℝ^(m + 2)) → (ℝ^(m + 2))} (hF : ContDiff ℝ 1 F) :
    ∫ x in Ω, divergenceE F x
      = ∫ x in frontier Ω, (⟪F x, ν x⟫ : ℝ) ∂(μHE[m + 1] : Measure (ℝ^(m + 2))) := by
  classical
  have hμfin := surfaceMeasure_frontier_lt_top hΩ
  obtain ⟨ι, hFin, c, r, hr, hcharts, f, hsub⟩ := hΩ.exists_smoothPartitionOfUnity
  -- the pieces of the partition
  set V : Option ι → (ℝ^(m + 2)) → (ℝ^(m + 2)) := fun i x => f i x • F x with hVdef
  have hUbdd : ∀ i : Option ι, Bornology.IsBounded (i.elim Ω (fun j => Metric.ball (c j) (r j))) := by
    rintro (_ | j)
    · exact hΩ.isBounded
    · exact Metric.isBounded_ball
  have hζcd : ∀ i, ContDiff ℝ 1 (⇑(f i)) := fun i => by
    have h := (f i).contMDiff; rw [contMDiff_iff_contDiff] at h; exact h.of_le (mod_cast le_top)
  have hζcs : ∀ i, HasCompactSupport (⇑(f i)) := fun i =>
    Metric.isCompact_iff_isClosed_bounded.mpr ⟨isClosed_tsupport _, (hUbdd i).subset (hsub i)⟩
  have hVcd : ∀ i, ContDiff ℝ 1 (V i) := fun i => (hζcd i).smul hF
  have hVcs : ∀ i, HasCompactSupport (V i) := fun i => (hζcs i).smul_right
  have hsum1 : ∀ x ∈ closure Ω, ∑ i, f i x = 1 := fun x hx => by
    have h := f.sum_eq_one hx; rwa [finsum_eq_sum_of_fintype] at h
  -- the volume-side decomposition: ∫_Ω div F = ∑ᵢ ∫_Ω div (V i)
  have hFeq : ∀ x ∈ Ω, divergenceE F x = divergenceE (fun y => ∑ i, V i y) x := fun x hx => by
    have hEq : F =ᶠ[nhds x] (fun y => ∑ i, V i y) := by
      filter_upwards [hΩ.isOpen.mem_nhds hx] with y hy
      simp only [hVdef, ← Finset.sum_smul, hsum1 y (subset_closure hy), one_smul]
    simp only [divergenceE]; rw [hEq.fderiv_eq]
  have hdecomp : ∫ x in Ω, divergenceE F x = ∑ i, ∫ x in Ω, divergenceE (V i) x := by
    rw [setIntegral_congr_fun hΩ.measurableSet hFeq]
    have hpt : ∀ x, divergenceE (fun y => ∑ i, V i y) x = ∑ i, divergenceE (V i) x := fun x =>
      divergenceE_finset_sum _ _ (fun i _ => (hVcd i).differentiable (by norm_num) x)
    simp_rw [hpt]
    rw [integral_finset_sum]
    exact fun i _ => ((continuous_divergenceE (hVcd i)).integrable_of_hasCompactSupport
      (hasCompactSupport_divergenceE (hVcd i) (hVcs i))).integrableOn
  have hFrmeas : MeasurableSet (frontier Ω) := isClosed_frontier.measurableSet
  have hVtsupp : ∀ i, tsupport (V i) ⊆ i.elim Ω (fun j => Metric.ball (c j) (r j)) := fun i =>
    subset_trans (closure_mono (Function.support_smul_subset_left (⇑(f i)) F)) (hsub i)
  have hfrΩ : ∀ x ∈ frontier Ω, x ∉ Ω := fun x hx hxΩ =>
    (show x ∈ closure Ω \ interior Ω from hx).2 (hΩ.isOpen.interior_eq.symm ▸ hxΩ)
  -- each piece: ∫_Ω div (V i) = ∫_{frontier} ⟪V i, ν⟫
  have hdivsupp : ∀ i, Function.support (fun x => divergenceE (V i) x)
      ⊆ i.elim Ω (fun j => Metric.ball (c j) (r j)) := fun i => by
    refine subset_trans (fun x hx => ?_) (hVtsupp i)
    by_contra hxts
    have hVe : V i =ᶠ[nhds x] 0 := notMem_tsupport_iff_eventuallyEq.mp hxts
    have hfd : fderiv ℝ (V i) x = 0 := by rw [hVe.fderiv_eq]; simp
    exact hx (by simp [divergenceE, hfd])
  have hchart_i : ∀ i, ∫ x in Ω, divergenceE (V i) x
      = ∫ x in frontier Ω, (⟪V i x, ν x⟫ : ℝ) ∂(μHE[m + 1] : Measure (ℝ^(m + 2))) := by
    rintro (_ | j)
    · have hL : ∫ x in Ω, divergenceE (V none) x = 0 := by
        rw [setIntegral_eq_of_support_subset hΩ.measurableSet MeasurableSet.univ (hdivsupp none)
          (by simp), setIntegral_univ]
        exact integral_divergenceE_eq_zero (hVcd none) (hVcs none)
      have hR : ∫ x in frontier Ω, (⟪V none x, ν x⟫ : ℝ) ∂μHE[m + 1] = 0 := by
        refine setIntegral_eq_zero_of_forall_eq_zero (fun x hx => ?_)
        have : V none x = 0 :=
          image_eq_zero_of_notMem_tsupport (fun hmem => hfrΩ x hx (hVtsupp none hmem))
        rw [this, inner_zero_left]
      rw [hL, hR]
    · obtain ⟨e, γ, hγcd, hchartj⟩ := hcharts j
      exact chart_term e (c j) hγcd hΩ.measurableSet hchartj
        (hν.eq_chart (c j) (r j) e γ hγcd hchartj) (hVcd (some j)) (hVcs (some j)) (hVtsupp (some j))
  -- surface measure of the boundary is finite (so the flux pieces are integrable)
  haveI : IsFiniteMeasure ((μHE[m + 1] : Measure (ℝ^(m + 2))).restrict (frontier Ω)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hμfin⟩
  have hfluxint : ∀ i, IntegrableOn (fun x => (⟪V i x, ν x⟫ : ℝ)) (frontier Ω)
      (μHE[m + 1] : Measure (ℝ^(m + 2))) := fun i =>
    ((hVcd i).continuous.inner hν.continuous).integrable_of_hasCompactSupport
      (μ := (μHE[m + 1]).restrict (frontier Ω))
      (HasCompactSupport.intro (hVcs i) (fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport hx, inner_zero_left]))
  -- assemble
  rw [hdecomp]
  simp_rw [hchart_i]
  rw [← integral_finset_sum _ (fun i _ => hfluxint i)]
  refine setIntegral_congr_fun hFrmeas (fun x hx => ?_)
  rw [← sum_inner]
  congr 1
  simp only [hVdef, ← Finset.sum_smul, hsum1 x (frontier_subset_closure hx), one_smul]


/-! ### The ball is a bounded C¹ domain (gate lemma for the Laplace representation formula) -/

/-- The fixed unit "height" vector: `flatten` reads off the coordinate `⟪·, heightVec⟫`. -/
def heightVec (m : ℕ) : ℝ^(m + 2) := flatten m (WithLp.toLp 2 ((0 : ℝ^(m + 1)), (1 : ℝ)))

/-- **Step A.** The height coordinate that `flatten.symm` extracts is the inner product with the
fixed unit vector `heightVec`. -/
lemma flatten_symm_snd (m : ℕ) (w : ℝ^(m + 2)) :
    (((flatten m).symm w).ofLp).2 = ⟪w, heightVec m⟫ := by
  have h := (flatten m).toLinearIsometry.inner_map_map ((flatten m).symm w)
    (WithLp.toLp 2 ((0 : ℝ^(m + 1)), (1 : ℝ)))
  simp only [LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.apply_symm_apply] at h
  have hone : (⟪((flatten m).symm w).snd, (1 : ℝ)⟫ : ℝ) = ((flatten m).symm w).snd := by
    have h2 := real_inner_smul_left (1 : ℝ) (1 : ℝ) (((flatten m).symm w).snd)
    simpa [real_inner_self_eq_norm_mul_norm] using h2
  rw [heightVec, h, WithLp.prod_inner_apply]
  simp [hone]

/-- **Step B.** In `ℝⁿ⁺¹` any unit vector rotates onto any other unit vector. -/
lemma exists_isometry_map_of_norm_one {n : ℕ} (u w : ℝ^(n + 1)) (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) :
    ∃ e : (ℝ^(n + 1)) ≃ₗᵢ[ℝ] (ℝ^(n + 1)), e u = w := by
  have hcard : Module.finrank ℝ (ℝ^(n + 1)) = Fintype.card (Fin (n + 1)) := by
    rw [finrank_euclideanSpace_fin, Fintype.card_fin]
  have hon : ∀ z : ℝ^(n + 1), ‖z‖ = 1 →
      Orthonormal ℝ (Set.restrict {(0 : Fin (n + 1))} (fun _ => z)) := by
    intro z hz
    rw [orthonormal_iff_ite]
    intro i j
    rw [Subsingleton.elim i j]
    simp [hz]
  obtain ⟨bu, hbu⟩ := (hon u hu).exists_orthonormalBasis_extension_of_card_eq hcard
  obtain ⟨bw, hbw⟩ := (hon w hw).exists_orthonormalBasis_extension_of_card_eq hcard
  refine ⟨bu.equiv bw (Equiv.refl (Fin (n + 1))), ?_⟩
  have hbu0 : bu 0 = u := hbu 0 (by simp)
  have hbw0 : bw 0 = w := hbw 0 (by simp)
  rw [← hbu0, OrthonormalBasis.equiv_apply_basis, Equiv.refl_apply, hbw0]

/-! ### Step D — the global `C¹` graph profile. -/

/-- Transition weight: `0` for `s ≤ r²/8`, `1` for `s ≥ r²/4`, smooth in between. -/
def ballT (r s : ℝ) : ℝ := Real.smoothTransition ((s - r ^ 2 / 8) / (r ^ 2 / 8))

/-- Smooth clamp: `= s` for `s ≤ r²/8`, and `≤ r²/2` everywhere. -/
def ballClamp (r s : ℝ) : ℝ := s * (1 - ballT r s) + r ^ 2 / 2 * ballT r s

/-- The globally `C¹` graph profile whose subgraph is the ball near a boundary point. -/
def ballProfile {m : ℕ} (r : ℝ) (b : ℝ^(m + 1)) : ℝ :=
  Real.sqrt (r ^ 2 - ballClamp r (‖b‖ ^ 2)) - r

lemma ballT_zero {r s : ℝ} (hr : 0 < r) (hs : s ≤ r ^ 2 / 8) : ballT r s = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  apply div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)

lemma ballClamp_eq {r s : ℝ} (hr : 0 < r) (hs : s ≤ r ^ 2 / 8) : ballClamp r s = s := by
  rw [ballClamp, ballT_zero hr hs]; ring

lemma ballClamp_le {r : ℝ} (hr : 0 < r) (s : ℝ) : ballClamp r s ≤ r ^ 2 / 2 := by
  have hT0 : 0 ≤ ballT r s := Real.smoothTransition.nonneg _
  have hT1 : ballT r s ≤ 1 := Real.smoothTransition.le_one _
  by_cases hle : s ≤ r ^ 2 / 2
  · rw [ballClamp]; nlinarith [hT0, hT1]
  · rw [not_le] at hle
    have hone : ballT r s = 1 := by
      apply Real.smoothTransition.one_of_one_le
      rw [le_div_iff₀ (by positivity)]; nlinarith
    rw [ballClamp, hone]; ring_nf; nlinarith

lemma radicand_pos {r : ℝ} (hr : 0 < r) (s : ℝ) : 0 < r ^ 2 - ballClamp r s := by
  have := ballClamp_le hr s; nlinarith

lemma contDiff_ballClamp (r : ℝ) : ContDiff ℝ 1 (ballClamp r) := by
  have hT : ContDiff ℝ 1 (fun s : ℝ => ballT r s) := by
    refine Real.smoothTransition.contDiff.comp ?_
    exact (contDiff_id.sub contDiff_const).div_const _
  exact (contDiff_id.mul (contDiff_const.sub hT)).add (contDiff_const.mul hT)

lemma contDiff_ballProfile {m : ℕ} (r : ℝ) (hr : 0 < r) :
    ContDiff ℝ 1 (ballProfile r (m := m)) := by
  have hrad : ContDiff ℝ 1 (fun b : ℝ^(m + 1) => r ^ 2 - ballClamp r (‖b‖ ^ 2)) :=
    contDiff_const.sub ((contDiff_ballClamp r).comp (contDiff_norm_sq ℝ))
  have hne : ∀ b : ℝ^(m + 1), r ^ 2 - ballClamp r (‖b‖ ^ 2) ≠ 0 :=
    fun b => (radicand_pos hr _).ne'
  exact (hrad.sqrt hne).sub contDiff_const

lemma ballProfile_eq {m : ℕ} {r : ℝ} (hr : 0 < r) (b : ℝ^(m + 1)) (hb : ‖b‖ ^ 2 ≤ r ^ 2 / 8) :
    ballProfile r b = Real.sqrt (r ^ 2 - ‖b‖ ^ 2) - r := by
  rw [ballProfile, ballClamp_eq hr hb]

set_option maxHeartbeats 1000000 in
-- The local set-equality repeatedly normalizes `EuclideanSpace`/`WithLp` projections, whose `whnf`
-- is slow enough to exceed the default heartbeat budget.
/-- **The open ball is a bounded `C¹` domain** (the gate lemma for Laplace representation). -/
theorem isBoundedC1Domain_ball {m : ℕ} (c : ℝ^(m + 2)) (r : ℝ) (hr : 0 < r) :
    IsBoundedC1Domain (Metric.ball c r) := by
  refine ⟨isOpen_ball, isBounded_ball, ?_⟩
  intro x₀ hx₀
  have hx0c : ‖x₀ - c‖ = r := by
    have hs : x₀ ∈ sphere c r := by rwa [frontier_ball c hr.ne'] at hx₀
    rw [← dist_eq_norm]; simpa [mem_sphere] using hs
  set u : ℝ^(m + 2) := r⁻¹ • (x₀ - c) with hudef
  have hunorm : ‖u‖ = 1 := by
    rw [hudef, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hr, hx0c, inv_mul_cancel₀ hr.ne']
  have hhv : ‖heightVec m‖ = 1 := by
    rw [heightVec, LinearIsometryEquiv.norm_map, WithLp.prod_norm_eq_of_L2]; simp
  obtain ⟨e, he⟩ := exists_isometry_map_of_norm_one u (heightVec m) hunorm hhv
  -- height and base as functions of `x`.
  have hheight : ∀ x : ℝ^(m + 2), ((flatten m).symm (e (x - x₀))).ofLp.2 = ⟪x - x₀, u⟫ := by
    intro x; rw [flatten_symm_snd, ← he, e.inner_map_map]
  have hnormid : ∀ x : ℝ^(m + 2),
      ‖((flatten m).symm (e (x - x₀))).ofLp.1‖ ^ 2 + (⟪x - x₀, u⟫ : ℝ) ^ 2 = ‖x - x₀‖ ^ 2 := by
    intro x
    have h1 : ‖(flatten m).symm (e (x - x₀))‖ = ‖x - x₀‖ := by
      rw [LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map]
    have h2 := WithLp.prod_norm_sq_eq_of_L2 ((flatten m).symm (e (x - x₀)))
    rw [h1, Real.norm_eq_abs, sq_abs,
      show ((flatten m).symm (e (x - x₀))).snd = (⟪x - x₀, u⟫ : ℝ) from hheight x] at h2
    rw [show ((flatten m).symm (e (x - x₀))).ofLp.1
        = ((flatten m).symm (e (x - x₀))).fst from rfl]
    linarith [h2]
  refine ⟨r / 3, by positivity, e, ballProfile r, contDiff_ballProfile r hr, ?_⟩
  -- the key local equivalence
  have key : ∀ x : ℝ^(m + 2), dist x x₀ < r / 3 →
      (dist x c < r ↔
        ((flatten m).symm (e (x - x₀))).ofLp.2 < ballProfile r ((flatten m).symm (e (x - x₀))).ofLp.1) := by
    intro x hxρ
    have hHeq : ((flatten m).symm (e (x - x₀))).ofLp.2 = ⟪x - x₀, u⟫ := hheight x
    set b : ℝ^(m + 1) := ((flatten m).symm (e (x - x₀))).ofLp.1 with hbdef
    set H : ℝ := ⟪x - x₀, u⟫ with hHdef
    have hxx0 : ‖x - x₀‖ < r / 3 := by rw [← dist_eq_norm]; exact hxρ
    have hbnorm : ‖b‖ ^ 2 + H ^ 2 = ‖x - x₀‖ ^ 2 := hnormid x
    have hb2 : ‖b‖ ^ 2 ≤ r ^ 2 / 8 := by nlinarith [sq_nonneg H, hxx0.le, norm_nonneg (x - x₀)]
    have hHle : |H| ≤ ‖x - x₀‖ := by
      have := abs_real_inner_le_norm (x - x₀) u
      rwa [hunorm, mul_one] at this
    have hHr : 0 < H + r := by
      have : -‖x - x₀‖ ≤ H := (abs_le.mp hHle).1
      nlinarith
    have hinner : (⟪x - x₀, x₀ - c⟫ : ℝ) = r * H := by
      have he' : H = r⁻¹ * ⟪x - x₀, x₀ - c⟫ := by rw [hHdef, hudef, real_inner_smul_right]
      rw [he']; field_simp
    have hdist2 : ‖x - c‖ ^ 2 = ‖b‖ ^ 2 + (H + r) ^ 2 := by
      have hxc : x - c = (x - x₀) + (x₀ - c) := by abel
      rw [hxc, norm_add_sq_real, hx0c, hinner]
      nlinarith [hbnorm]
    rw [dist_eq_norm, hHeq, ballProfile_eq hr b hb2]
    constructor
    · intro hlt
      have h2 : ‖x - c‖ ^ 2 < r ^ 2 := by nlinarith [norm_nonneg (x - c)]
      rw [hdist2] at h2
      have h3 : (H + r) ^ 2 < r ^ 2 - ‖b‖ ^ 2 := by nlinarith
      have := (Real.lt_sqrt hHr.le).mpr h3
      linarith
    · intro hlt
      have hs : H + r < Real.sqrt (r ^ 2 - ‖b‖ ^ 2) := by linarith
      have h3 := (Real.lt_sqrt hHr.le).mp hs
      have h2 : ‖x - c‖ ^ 2 < r ^ 2 := by rw [hdist2]; nlinarith
      nlinarith [norm_nonneg (x - c), sq_nonneg (‖x - c‖ - r)]
  ext x
  simp only [mem_inter_iff, mem_ball, mem_setOf_eq]
  constructor
  · rintro ⟨hxc, hxρ⟩; exact ⟨(key x hxρ).mp hxc, hxρ⟩
  · rintro ⟨hsub, hxρ⟩; exact ⟨(key x hxρ).mpr hsub, hxρ⟩


/-! ### The outward normal of the ball (chart-independence of the graph normal)

The `IsOutwardNormal` structure requires the field `ν` to match the chart normal
`e.symm (flatten (graphNormal γ (base x)))` for *every* chart representing the domain as a
subgraph. Establishing this for the ball is a genuine geometric-uniqueness statement: the unit
normal to a `C¹` hypersurface is determined by the surface (up to the side singled out by the
domain). We prove it by

* showing the chart normal is orthogonal to every graph tangent (`chartNormalRaw_perp_tangent`);
* showing the radial vector `x - center` is orthogonal to every graph tangent, by differentiating
  the (locally constant) `‖Ψ(·) - center‖²` along the graph parametrization (`centerVec_perp_tangent`);
* concluding the two are colinear, since the orthogonal complement of the `(m+1)`-dimensional tangent
  space is a line (`chartNormal_eq_outward`); and
* fixing the sign by differentiating the defining function along the outward radial direction, whose
  right-derivative is `≥ 0` because the ball lies on the `height < γ` side (`outward_sign`). -/

/-- The un-normalized chart normal in ambient coordinates. -/
def chartNormalRaw (e : (ℝ^(m + 2)) ≃ₗᵢ[ℝ] (ℝ^(m + 2))) (a : ℝ^(m + 1)) : ℝ^(m + 2) :=
  e.symm (flatten m (WithLp.toLp 2 ((-a : ℝ^(m + 1)), (1 : ℝ))))

/-- The tangent map of the graph chart at base point with gradient `a`. -/
def chartTangent (e : (ℝ^(m + 2)) ≃ₗᵢ[ℝ] (ℝ^(m + 2))) (a : ℝ^(m + 1)) (h : ℝ^(m + 1)) :
    ℝ^(m + 2) :=
  e.symm (flatten m (WithLp.toLp 2 (h, (⟪a, h⟫ : ℝ))))

/-- The raw chart normal is orthogonal to every tangent vector. -/
lemma chartNormalRaw_perp_tangent (e : (ℝ^(m + 2)) ≃ₗᵢ[ℝ] (ℝ^(m + 2))) (a h : ℝ^(m + 1)) :
    ⟪chartNormalRaw e a, chartTangent e a h⟫ = 0 := by
  rw [chartNormalRaw, chartTangent, e.symm.inner_map_map, (flatten m).inner_map_map,
    WithLp.prod_inner_apply]
  simp only [inner_neg_left]
  have key : (⟪(1:ℝ), (⟪a, h⟫ : ℝ)⟫ : ℝ) = ⟪a, h⟫ := by
    conv_lhs => rw [show (⟪a, h⟫ : ℝ) = (⟪a, h⟫ : ℝ) • (1:ℝ) by rw [smul_eq_mul, mul_one]]
    rw [real_inner_smul_right, real_inner_self_eq_norm_mul_norm, norm_one, mul_one, mul_one]
  rw [key]; ring

/-- The norm of the raw chart normal is `√(1 + ‖a‖²)`. -/
lemma chartNormalRaw_norm (e : (ℝ^(m + 2)) ≃ₗᵢ[ℝ] (ℝ^(m + 2))) (a : ℝ^(m + 1)) :
    ‖chartNormalRaw e a‖ = Real.sqrt (1 + ‖a‖ ^ 2) := by
  rw [chartNormalRaw, e.symm.norm_map, (flatten m).norm_map, WithLp.prod_norm_eq_of_L2]
  congr 1
  change ‖(-a : ℝ^(m + 1))‖ ^ 2 + ‖(1:ℝ)‖ ^ 2 = 1 + ‖a‖ ^ 2
  rw [norm_neg, norm_one]; ring

/-- The `graphNormal`-based chart normal is a positive multiple of the raw normal. -/
lemma chartNormal_expand (e : (ℝ^(m + 2)) ≃ₗᵢ[ℝ] (ℝ^(m + 2))) (γ : (ℝ^(m + 1)) → ℝ)
    (b : ℝ^(m + 1)) :
    e.symm (flatten m (graphNormal γ b))
      = (Real.sqrt (1 + ‖gradient γ b‖ ^ 2))⁻¹ • chartNormalRaw e (gradient γ b) := by
  rw [graphNormal, chartNormalRaw, map_smul, map_smul]

/-- The tangent map of the graph chart, as a linear map. -/
def chartTangentMap (e : (ℝ^(m + 2)) ≃ₗᵢ[ℝ] (ℝ^(m + 2))) (a : ℝ^(m + 1)) :
    (ℝ^(m + 1)) →ₗ[ℝ] (ℝ^(m + 2)) :=
  e.symm.toLinearIsometry.toLinearMap ∘ₗ (flatten m).toLinearIsometry.toLinearMap ∘ₗ graphMap a

lemma chartTangentMap_apply (e : (ℝ^(m + 2)) ≃ₗᵢ[ℝ] (ℝ^(m + 2))) (a h : ℝ^(m + 1)) :
    chartTangentMap e a h = chartTangent e a h := by
  simp only [chartTangentMap, LinearMap.comp_apply, LinearIsometry.coe_toLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry, chartTangent]
  rfl

lemma chartTangentMap_injective (e : (ℝ^(m + 2)) ≃ₗᵢ[ℝ] (ℝ^(m + 2))) (a : ℝ^(m + 1)) :
    Function.Injective (chartTangentMap e a) := by
  intro x y h
  simp only [chartTangentMap, LinearMap.comp_apply, LinearIsometry.coe_toLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry] at h
  exact graph_injective a ((flatten m).injective (e.symm.injective h))

lemma chartTangentMap_finrank_range (e : (ℝ^(m + 2)) ≃ₗᵢ[ℝ] (ℝ^(m + 2))) (a : ℝ^(m + 1)) :
    Module.finrank ℝ (LinearMap.range (chartTangentMap e a)) = m + 1 := by
  rw [LinearMap.finrank_range_of_inj (chartTangentMap_injective e a), finrank_euclideanSpace_fin]

set_option maxHeartbeats 1000000 in
-- The `fderiv`/`WithLp`/`EuclideanSpace` manipulation here repeatedly forces slow `whnf`
-- normalization of projections, exceeding the default heartbeat budget.
/-- **Geometric orthogonality.** If a ball's frontier is locally the graph of `γ` in a chart, then
at a frontier point `x` the radial vector `x - center` is orthogonal to every graph tangent. -/
lemma centerVec_perp_tangent
    (center : ℝ^(m + 2)) (r : ℝ) (hr : 0 < r)
    (c : ℝ^(m + 2)) (ρ : ℝ) (e : (ℝ^(m + 2)) ≃ₗᵢ[ℝ] (ℝ^(m + 2))) (γ : (ℝ^(m + 1)) → ℝ)
    (hγ : ContDiff ℝ 1 γ)
    (hchart : Metric.ball center r ∩ Metric.ball c ρ
      = {x | ((flatten m).symm (e (x - c))).ofLp.2 < γ ((flatten m).symm (e (x - c))).ofLp.1}
        ∩ Metric.ball c ρ)
    (x : ℝ^(m + 2)) (hxf : x ∈ frontier (Metric.ball center r)) (hxb : x ∈ Metric.ball c ρ)
    (h : ℝ^(m + 1)) :
    (⟪x - center, chartTangent e (gradient γ ((flatten m).symm (e (x - c))).ofLp.1) h⟫ : ℝ) = 0 := by
  set b := ((flatten m).symm (e (x - c))).ofLp.1 with hb
  have hofLp1 : ∀ y : ℝ^(m + 1), (graphFun γ y).ofLp.1 = y := fun _ => rfl
  have hofLp2 : ∀ y : ℝ^(m + 1), (graphFun γ y).ofLp.2 = γ y := fun _ => rfl
  -- x lies on the graph
  have hxgraph : ((flatten m).symm (e (x - c))).ofLp.2 = γ b := by
    have hmem : x ∈ frontier (Metric.ball center r) ∩ Metric.ball c ρ := ⟨hxf, hxb⟩
    rw [chart_frontier_domain e c hγ.continuous hchart] at hmem
    exact hmem.1
  -- the graph parametrization
  set Ψ : (ℝ^(m + 1)) → (ℝ^(m + 2)) := fun b' => c + e.symm (flatten m (graphFun γ b')) with hΨ
  have hΨcont : Continuous Ψ := continuous_const.add
    (e.symm.continuous.comp ((flatten m).continuous.comp (continuous_graphFun hγ.continuous)))
  have hbase : ∀ b', (flatten m).symm (e (Ψ b' - c)) = graphFun γ b' := by
    intro b'
    simp only [hΨ, add_sub_cancel_left, LinearIsometryEquiv.apply_symm_apply,
      LinearIsometryEquiv.symm_apply_apply]
  have hgf_b : graphFun γ b = (flatten m).symm (e (x - c)) := by
    apply WithLp.ofLp_injective 2
    show (graphFun γ b).ofLp = ((flatten m).symm (e (x - c))).ofLp
    exact Prod.ext_iff.mpr ⟨hb, hxgraph.symm⟩
  have hΨx : Ψ b = x := by
    have hxc : e.symm (flatten m (graphFun γ b)) = x - c := by
      rw [hgf_b, LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.symm_apply_apply]
    show c + e.symm (flatten m (graphFun γ b)) = x
    rw [hxc]; abel
  -- Ψ b' stays in the chart ball near b
  have hΨmem : ∀ᶠ b' in nhds b, Ψ b' ∈ Metric.ball c ρ :=
    (hΨcont.continuousAt).preimage_mem_nhds (Metric.isOpen_ball.mem_nhds (hΨx ▸ hxb))
  -- ‖Ψ b' - center‖² is eventually r²
  have hev : ∀ᶠ b' in nhds b, ‖Ψ b' - center‖ ^ 2 = r ^ 2 := by
    filter_upwards [hΨmem] with b' hb'mem
    have hmem2 : Ψ b' ∈ frontier (Metric.ball center r) ∩ Metric.ball c ρ := by
      rw [chart_frontier_domain e c hγ.continuous hchart]
      refine ⟨?_, hb'mem⟩
      simp only [Set.mem_setOf_eq, hbase b', hofLp1, hofLp2]
    have hnorm : ‖Ψ b' - center‖ = r := by
      have hs := hmem2.1
      rw [frontier_ball center hr.ne'] at hs
      rw [← dist_eq_norm]; simpa [mem_sphere] using hs
    rw [hnorm]
  -- HasFDerivAt of Ψ
  set fltCLM := (flatten m).toLinearIsometry.toContinuousLinearMap with hfltCLM
  set esymCLM := e.symm.toLinearIsometry.toContinuousLinearMap with hesymCLM
  set L := esymCLM.comp (fltCLM.comp (graphFun' γ b)) with hL
  have hΨf : HasFDerivAt Ψ L b := by
    have hcomp := esymCLM.hasFDerivAt.comp b (fltCLM.hasFDerivAt.comp b (hasFDerivAt_graphFun hγ b))
    refine (hcomp.const_add c).congr_of_eventuallyEq (Filter.Eventually.of_forall (fun b' => ?_))
    simp only [hΨ, Function.comp_apply, hesymCLM, hfltCLM,
      LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry]
  have hLapply : L h = chartTangent e (gradient γ b) h := by
    have hgfd : (graphFun' γ b) h = WithLp.toLp 2 (h, (⟪gradient γ b, h⟫ : ℝ)) := by
      rw [graphFun']
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
        ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply]
      rw [← inner_gradient_left (hγ.differentiable (by norm_num) b)]
      rfl
    simp only [hL, ContinuousLinearMap.comp_apply, hgfd, hfltCLM, hesymCLM,
      LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
      chartTangent]
  -- differentiate ‖Ψ · - center‖²
  have hsub : HasFDerivAt (fun b' => Ψ b' - center) L b := hΨf.sub_const center
  have hnormsq := hsub.norm_sq
  have hconst : HasFDerivAt (fun b' => ‖Ψ b' - center‖ ^ 2) (0 : (ℝ^(m + 1)) →L[ℝ] ℝ) b :=
    (hasFDerivAt_const (r ^ 2) b).congr_of_eventuallyEq hev
  have hderiv0 := hnormsq.unique hconst
  have happ := congrFun (congrArg (DFunLike.coe) hderiv0) h
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    ContinuousLinearMap.zero_apply] at happ
  rw [hΨx] at happ
  rw [← hLapply]
  simpa using happ

/-- The inner product of the raw chart normal with any vector, read off in chart coordinates. -/
lemma chartNormalRaw_inner (e : (ℝ^(m + 2)) ≃ₗᵢ[ℝ] (ℝ^(m + 2))) (a : ℝ^(m + 1)) (v : ℝ^(m + 2)) :
    (⟪chartNormalRaw e a, v⟫ : ℝ)
      = ((flatten m).symm (e v)).ofLp.2 - ⟪a, ((flatten m).symm (e v)).ofLp.1⟫ := by
  rw [chartNormalRaw,
    ← e.inner_map_map (e.symm (flatten m (WithLp.toLp 2 ((-a : ℝ^(m + 1)), (1:ℝ))))) v,
    e.apply_symm_apply]
  conv_lhs => rw [← (flatten m).apply_symm_apply (e v), (flatten m).inner_map_map]
  rw [WithLp.prod_inner_apply]
  simp only [inner_neg_left]
  have key : (⟪(1:ℝ), (((flatten m).symm (e v)).ofLp.2 : ℝ)⟫ : ℝ)
      = ((flatten m).symm (e v)).ofLp.2 := by
    conv_lhs => rw [show (((flatten m).symm (e v)).ofLp.2 : ℝ)
      = (((flatten m).symm (e v)).ofLp.2) • (1:ℝ) by rw [smul_eq_mul, mul_one]]
    rw [real_inner_smul_right, real_inner_self_eq_norm_mul_norm, norm_one, mul_one, mul_one]
  rw [key]; ring

set_option maxHeartbeats 1000000 in
-- The `HasDerivAt`/`WithLp`/`EuclideanSpace` manipulation here repeatedly forces slow `whnf`
-- normalization of projections, exceeding the default heartbeat budget.
/-- **Outward sign.** At a boundary point of the ball, the raw chart normal has non-negative inner
product with the outward radial vector `x - center` — this fixes the sign of the unit normal. -/
lemma outward_sign
    (center : ℝ^(m + 2)) (r : ℝ) (hr : 0 < r)
    (c : ℝ^(m + 2)) (ρ : ℝ) (e : (ℝ^(m + 2)) ≃ₗᵢ[ℝ] (ℝ^(m + 2))) (γ : (ℝ^(m + 1)) → ℝ)
    (hγ : ContDiff ℝ 1 γ)
    (hchart : Metric.ball center r ∩ Metric.ball c ρ
      = {x | ((flatten m).symm (e (x - c))).ofLp.2 < γ ((flatten m).symm (e (x - c))).ofLp.1}
        ∩ Metric.ball c ρ)
    (x : ℝ^(m + 2)) (hxf : x ∈ frontier (Metric.ball center r)) (hxb : x ∈ Metric.ball c ρ) :
    0 ≤ (⟪chartNormalRaw e (gradient γ ((flatten m).symm (e (x - c))).ofLp.1), x - center⟫ : ℝ) := by
  set b := ((flatten m).symm (e (x - c))).ofLp.1 with hb
  set d := x - center with hd
  set M := chartNormalRaw e (gradient γ b) with hM
  set w := e.symm (heightVec m) with hw
  set β := ((flatten m).symm (e d)).ofLp.1 with hβ
  set φ : (ℝ^(m + 2)) → ℝ := fun y =>
    ((flatten m).symm (e (y - c))).ofLp.2 - γ ((flatten m).symm (e (y - c))).ofLp.1 with hφ
  have hx0c : ‖d‖ = r := by
    have hs : x ∈ sphere center r := by rwa [frontier_ball center hr.ne'] at hxf
    rw [hd, ← dist_eq_norm]; simpa [mem_sphere] using hs
  have hxgraph : ((flatten m).symm (e (x - c))).ofLp.2 = γ b := by
    have hmem : x ∈ frontier (Metric.ball center r) ∩ Metric.ball c ρ := ⟨hxf, hxb⟩
    rw [chart_frontier_domain e c hγ.continuous hchart] at hmem
    exact hmem.1
  have hφx : φ x = 0 := by
    simp only [hφ]; rw [hxgraph, ← hb]; ring
  -- adjoint identity for the height coordinate
  have hheightexpr : ∀ v : ℝ^(m + 2), ((flatten m).symm (e v)).ofLp.2 = ⟪v, w⟫ := by
    intro v
    rw [flatten_symm_snd, hw, ← e.inner_map_map v (e.symm (heightVec m)), e.apply_symm_apply]
  -- HasDerivAt of φ along the radial line
  have hheight : HasDerivAt (fun t : ℝ => ((flatten m).symm (e (x + t • d - c))).ofLp.2)
      (⟪d, w⟫) 0 := by
    have heq : (fun t : ℝ => ((flatten m).symm (e (x + t • d - c))).ofLp.2)
        = fun t => ⟪x - c, w⟫ + t * ⟪d, w⟫ := by
      funext t
      rw [hheightexpr, show x + t • d - c = (x - c) + t • d by abel, inner_add_left,
        real_inner_smul_left]
    rw [heq]
    simpa using ((hasDerivAt_id (x := (0:ℝ))).mul_const (⟪d, w⟫ : ℝ)).const_add (⟪x - c, w⟫ : ℝ)
  have hbaseeq : (fun t : ℝ => ((flatten m).symm (e (x + t • d - c))).ofLp.1)
      = fun t => b + t • β := by
    funext t
    rw [show x + t • d - c = (x - c) + t • d by abel, map_add, map_smul, map_add, map_smul]
    simp only [WithLp.ofLp_add, WithLp.ofLp_smul, Prod.fst_add, Prod.smul_fst, ← hb, ← hβ]
  have hgamma : HasDerivAt (fun t : ℝ => γ ((flatten m).symm (e (x + t • d - c))).ofLp.1)
      (⟪gradient γ b, β⟫) 0 := by
    have hfun : (fun t : ℝ => γ ((flatten m).symm (e (x + t • d - c))).ofLp.1)
        = fun t : ℝ => γ (b + t • β) := by
      funext t; rw [congrFun hbaseeq t]
    rw [hfun]
    have hd0 : HasDerivAt (fun t : ℝ => b + t • β) β 0 := by
      simpa using ((hasDerivAt_id (x := (0:ℝ))).smul_const β).const_add b
    have hgd : HasFDerivAt γ (fderiv ℝ γ (b + (0:ℝ) • β)) (b + (0:ℝ) • β) :=
      (hγ.differentiable (by norm_num) _).hasFDerivAt
    have hcomp := hgd.comp_hasDerivAt (0:ℝ) hd0
    simp only [zero_smul, add_zero] at hcomp
    rw [inner_gradient_left (hγ.differentiable (by norm_num) b)]
    exact hcomp
  have hφderiv : HasDerivAt (fun t : ℝ => φ (x + t • d)) (⟪d, w⟫ - ⟪gradient γ b, β⟫) 0 := by
    simp only [hφ]; exact hheight.sub hgamma
  -- ⟪M, d⟫ equals the derivative value
  have hdw : ((flatten m).symm (e d)).ofLp.2 = ⟪d, w⟫ := hheightexpr d
  have hMd : (⟪M, d⟫ : ℝ) = ⟪d, w⟫ - ⟪gradient γ b, β⟫ := by
    rw [hM, chartNormalRaw_inner, hdw, ← hβ]
  -- φ ≥ 0 just outside the ball
  have hnn : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), 0 ≤ φ (x + t • d) := by
    have hballρ : ∀ᶠ t in 𝓝 (0:ℝ), x + t • d ∈ Metric.ball c ρ := by
      have hcont : ContinuousAt (fun t : ℝ => x + t • d) 0 := by fun_prop
      have hx0 : x + (0:ℝ) • d ∈ Metric.ball c ρ := by simpa using hxb
      exact hcont.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds hx0)
    filter_upwards [hballρ.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t htρ htpos
    have htpos' : (0:ℝ) < t := htpos
    have hnotin : x + t • d ∉ Metric.ball center r := by
      rw [Metric.mem_ball, not_lt, dist_eq_norm]
      have hcalc : x + t • d - center = (1 + t) • d := by rw [hd]; module
      rw [hcalc, norm_smul, hx0c, Real.norm_eq_abs, abs_of_pos (by linarith)]
      nlinarith
    have hnotsub : x + t • d ∉ {y : ℝ^(m + 2) |
        ((flatten m).symm (e (y - c))).ofLp.2 < γ ((flatten m).symm (e (y - c))).ofLp.1} := by
      intro hsub
      have hmem : x + t • d ∈ Metric.ball center r ∩ Metric.ball c ρ :=
        hchart.symm ▸ Set.mem_inter hsub htρ
      exact hnotin hmem.1
    rw [Set.mem_setOf_eq, not_lt] at hnotsub
    simp only [hφ]; linarith [hnotsub]
  -- the right-derivative of φ along the line is ≥ 0
  have hDnn : 0 ≤ (⟪d, w⟫ - ⟪gradient γ b, β⟫ : ℝ) := by
    have hslope := hφderiv.hasDerivWithinAt (s := Set.Ioi 0)
    rw [hasDerivWithinAt_iff_tendsto_slope] at hslope
    have hset : Set.Ioi (0:ℝ) \ {0} = Set.Ioi 0 := by
      ext s; simp only [Set.mem_diff, Set.mem_Ioi, Set.mem_singleton_iff]
      exact ⟨fun h => h.1, fun h => ⟨h, ne_of_gt h⟩⟩
    rw [hset] at hslope
    refine ge_of_tendsto hslope ?_
    filter_upwards [hnn, self_mem_nhdsWithin] with t ht htmem
    have htpos : (0:ℝ) < t := htmem
    have hval : slope (fun s : ℝ => φ (x + s • d)) 0 t = φ (x + t • d) / t := by
      simp only [slope_def_field, sub_zero, zero_smul, add_zero, hφx]
    rw [hval]
    exact div_nonneg ht htpos.le
  rw [hMd]; exact hDnn

set_option maxHeartbeats 1000000 in
-- The colinearity/finrank and `WithLp`/`EuclideanSpace` manipulation here repeatedly forces slow
-- `whnf` normalization of projections, exceeding the default heartbeat budget.
/-- **Chart normal is the geometric outward normal.** For any chart representing the ball as a
subgraph, at a boundary point the chart normal equals the outward radial unit vector. -/
theorem chartNormal_eq_outward
    (center : ℝ^(m + 2)) (r : ℝ) (hr : 0 < r)
    (c : ℝ^(m + 2)) (ρ : ℝ) (e : (ℝ^(m + 2)) ≃ₗᵢ[ℝ] (ℝ^(m + 2))) (γ : (ℝ^(m + 1)) → ℝ)
    (hγ : ContDiff ℝ 1 γ)
    (hchart : Metric.ball center r ∩ Metric.ball c ρ
      = {x | ((flatten m).symm (e (x - c))).ofLp.2 < γ ((flatten m).symm (e (x - c))).ofLp.1}
        ∩ Metric.ball c ρ)
    (x : ℝ^(m + 2)) (hxf : x ∈ frontier (Metric.ball center r)) (hxb : x ∈ Metric.ball c ρ) :
    r⁻¹ • (x - center)
      = e.symm (flatten m (graphNormal γ ((flatten m).symm (e (x - c))).ofLp.1)) := by
  set b := ((flatten m).symm (e (x - c))).ofLp.1 with hb
  set a := gradient γ b with ha
  set sq := Real.sqrt (1 + ‖a‖ ^ 2) with hsq
  have hsqpos : 0 < sq := Real.sqrt_pos.mpr (by positivity)
  set Nu := e.symm (flatten m (graphNormal γ b)) with hNu
  set g := r⁻¹ • (x - center) with hg
  have hNuexp : Nu = sq⁻¹ • chartNormalRaw e a := chartNormal_expand e γ b
  have hx0c : ‖x - center‖ = r := by
    have hs : x ∈ sphere center r := by rwa [frontier_ball center hr.ne'] at hxf
    rw [← dist_eq_norm]; simpa [mem_sphere] using hs
  have hgnorm : ‖g‖ = 1 := by
    rw [hg, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hr, hx0c, inv_mul_cancel₀ hr.ne']
  have hNunorm : ‖Nu‖ = 1 := by
    rw [hNu, e.symm.norm_map, (flatten m).norm_map, norm_graphNormal]
  set T := chartTangentMap e a with hT
  set W := LinearMap.range T with hW
  have hWrank : Module.finrank ℝ W = m + 1 := chartTangentMap_finrank_range e a
  have hNuperp : Nu ∈ Wᗮ := by
    rw [Submodule.mem_orthogonal']
    intro u hu
    obtain ⟨h', rfl⟩ := LinearMap.mem_range.mp hu
    rw [hT, chartTangentMap_apply, hNuexp, real_inner_smul_left, chartNormalRaw_perp_tangent,
      mul_zero]
  have hgperp : g ∈ Wᗮ := by
    rw [Submodule.mem_orthogonal']
    intro u hu
    obtain ⟨h', rfl⟩ := LinearMap.mem_range.mp hu
    have hperp := centerVec_perp_tangent center r hr c ρ e γ hγ hchart x hxf hxb h'
    rw [hT, chartTangentMap_apply, hg, real_inner_smul_left, hperp, mul_zero]
  have hWperp_rank : Module.finrank ℝ (Wᗮ) = 1 := by
    have h := W.finrank_add_finrank_orthogonal
    rw [hWrank, finrank_euclideanSpace_fin] at h
    omega
  have hNune : (⟨Nu, hNuperp⟩ : (Wᗮ)) ≠ 0 := by
    intro h0
    have hz : Nu = 0 := congrArg Subtype.val h0
    rw [hz, norm_zero] at hNunorm
    exact one_ne_zero hNunorm.symm
  obtain ⟨t, ht⟩ := (finrank_eq_one_iff_of_nonzero' (⟨Nu, hNuperp⟩ : (Wᗮ)) hNune).mp
    hWperp_rank ⟨g, hgperp⟩
  have htg : t • Nu = g := by
    have h := congrArg (Subtype.val) ht
    simpa using h
  have habs : |t| = 1 := by
    have hn : ‖g‖ = |t| * ‖Nu‖ := by rw [← htg, norm_smul, Real.norm_eq_abs]
    rw [hgnorm, hNunorm, mul_one] at hn
    exact hn.symm
  -- sign
  have hMxc : 0 ≤ (⟪chartNormalRaw e a, x - center⟫ : ℝ) :=
    outward_sign center r hr c ρ e γ hγ hchart x hxf hxb
  have hgxc : (⟪g, x - center⟫ : ℝ) = r := by
    rw [hg, real_inner_smul_left, real_inner_self_eq_norm_mul_norm, hx0c, ← mul_assoc,
      inv_mul_cancel₀ hr.ne', one_mul]
  have hgxc2 : (⟪g, x - center⟫ : ℝ) = t * (sq⁻¹ * ⟪chartNormalRaw e a, x - center⟫) := by
    rw [← htg, hNuexp, real_inner_smul_left, real_inner_smul_left]
  have htpos : 0 < t := by
    have hbnn : 0 ≤ sq⁻¹ * (⟪chartNormalRaw e a, x - center⟫ : ℝ) :=
      mul_nonneg (inv_nonneg.mpr hsqpos.le) hMxc
    nlinarith [hgxc, hgxc2, hbnn, hr]
  have ht1 : t = 1 := by
    rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp habs with h | h
    · exact h
    · linarith
  rw [← htg, ht1, one_smul]

/-- **The outward unit normal of a ball.** `ν(y) = r⁻¹ (y − center)` is an `IsOutwardNormal`. -/
theorem isOutwardNormal_ball (center : ℝ^(m + 2)) (r : ℝ) (hr : 0 < r) :
    IsOutwardNormal (Metric.ball center r) (fun y => r⁻¹ • (y - center)) := by
  refine ⟨continuous_const.smul (continuous_id.sub continuous_const), ?_⟩
  intro c ρ e γ hγ hchart y hy
  exact chartNormal_eq_outward center r hr c ρ e γ hγ hchart y hy.1 hy.2


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

end AreaFormula

end

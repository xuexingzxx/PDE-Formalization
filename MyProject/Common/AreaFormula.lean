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
open scoped ENNReal NNReal RealInnerProductSpace Pointwise

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

end AreaFormula

end

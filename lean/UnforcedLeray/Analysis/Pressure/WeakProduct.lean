import UnforcedLeray.Analysis.LerayProjection.Mollifier.Representative
import UnforcedLeray.Analysis.EnergyInterpolation.Stress
import UnforcedLeray.Analysis.Pressure.VelocityForcing

/-!
# The actual weak quadratic product identity for H¹ velocities

A solenoidal L² field is tested against a compact smooth test times a smooth
mollification of one velocity component. Strong L² convergence of that
component and its weak derivatives then passes the identity to the actual
H¹ field. Every product pairing is justified by Hölder integrability.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff ENNReal

namespace UnforcedLeray.PressureAnalysis

/-- A bounded scalar weight times one L² coordinate is genuinely square integrable. -/
theorem weighted_coordinate_memLp {u : SpatialField} {ψ : Space → ℝ}
    (hu : MemLp u 2 volume) (hψ : MemLp ψ ⊤ volume) (j : Fin 3) :
    MemLp (fun x => ψ x * u x j) 2 volume := by
  exact (EnergyInterpolation.coordinate_memLp hu j).mul' hψ

/-- All bounded-weight quadratic coordinate pairings are actual integrable functions. -/
theorem weighted_product_integrable {u v : SpatialField} {ψ : Space → ℝ}
    (hu : MemLp u 2 volume) (hv : MemLp v 2 volume) (hψ : MemLp ψ ⊤ volume)
    (j i : Fin 3) : Integrable (fun x => ψ x * u x j * v x i) volume := by
  apply memLp_one_iff_integrable.mp
  exact (EnergyInterpolation.coordinate_memLp hv i).mul'
    (weighted_coordinate_memLp hu hψ j)

/-- Pairing a moving L² coordinate with a fixed weighted L² coordinate is continuous. -/
def weightedCoordinatePairing {u : SpatialField} {ψ : Space → ℝ}
    (hu : MemLp u 2 volume) (hψ : MemLp ψ ⊤ volume) (j i : Fin 3) :
    L2Space →L[ℝ] ℝ :=
  (innerSL ℝ ((weighted_coordinate_memLp hu hψ j).toLp (fun x => ψ x * u x j))).comp
    ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) i).compLpL 2 volume)

/-- The continuous pairing is exactly its literal scalar Lebesgue integral. -/
theorem weightedCoordinatePairing_apply {u : SpatialField} {ψ : Space → ℝ}
    (hu : MemLp u 2 volume) (hψ : MemLp ψ ⊤ volume) (j i : Fin 3) (F : L2Space) :
    weightedCoordinatePairing hu hψ j i F = ∫ x, ψ x * u x j * F x i := by
  change inner ℝ ((weighted_coordinate_memLp hu hψ j).toLp (fun x => ψ x * u x j))
    ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) i).compLpL 2 volume F) = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(weighted_coordinate_memLp hu hψ j).coeFn_toLp,
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) i).coeFn_compLpL F] with x hx hy
  rw [hx, hy]
  change (F x i) * (ψ x * u x j) = ψ x * u x j * F x i
  ring

/-- The concrete smooth mollifications converge in every fixed weighted product pairing. -/
theorem weighted_product_mollification_tendsto {u v : SpatialField} {ψ : Space → ℝ}
    (hu : MemLp u 2 volume) (hv : MemLp v 2 volume) (hψ : MemLp ψ ⊤ volume)
    (j i : Fin 3) :
    Tendsto (fun n => ∫ x, ψ x * u x j *
      SobolevEmbedding.mollification (SobolevEmbedding.shrinkingMollifier n) v x i)
      atTop (𝓝 (∫ x, ψ x * u x j * v x i)) := by
  have h := (weightedCoordinatePairing hu hψ j i).continuous.tendsto (toL2 v)
    |>.comp (Leray.mollification_toL2_tendsto hv)
  have he (w : SpatialField) (hw : MemLp w 2 volume) :
      weightedCoordinatePairing hu hψ j i (toL2 w) = ∫ x, ψ x * u x j * w x i := by
    rw [weightedCoordinatePairing_apply]
    apply integral_congr_ae
    filter_upwards [coeFn_toL2 hw] with x hx
    rw [hx]
  simpa only [Function.comp_def, he _ hv, he _ (SobolevEmbedding.mollification_memLp _ _ hv)] using h

/-- Multiplying a spatial test by a smooth coordinate remains a spatial test. -/
theorem spatialTest_mul_coordinate {φ : Space → ℝ} {v : SpatialField}
    (hφ : IsSpatialTest φ) (hv : ContDiff ℝ ∞ v) (i : Fin 3) :
    IsSpatialTest (fun x => φ x * v x i) := by
  refine ⟨hφ.smooth.mul ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) i).contDiff.comp hv), ?_⟩
  exact hφ.compact.mul_right

/-- The actual classical derivative of the test-coordinate product. -/
theorem spatialTestDerivative_mul_coordinate {φ : Space → ℝ} {v : SpatialField}
    (hφ : IsSpatialTest φ) (hv : ContDiff ℝ ∞ v) (i j : Fin 3) (x : Space) :
    spatialTestDerivative j (fun y => φ y * v y i) x =
      spatialTestDerivative j φ x * v x i +
        φ x * (fderiv ℝ v x (coordinateVector j)) i := by
  have hp := (hφ.smooth.differentiable (by simp) x).hasFDerivAt
  have hv' := (hv.differentiable (by simp) x).hasFDerivAt
  have hi := (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) i).hasFDerivAt.comp x hv'
  change fderiv ℝ (fun y => φ y * v y i) x (coordinateVector j) = _
  have hprod := hp.mul hi
  change HasFDerivAt (fun y => φ y * v y i) _ x at hprod
  rw [hprod.fderiv]
  simp [spatialTestDerivative, EuclideanSpace.proj, PiLp.proj, PiLp.projₗ,
    mul_comm, add_comm]

/-- Weak solenoidality tested against a mollified coordinate gives an honest
quadratic identity before taking any limit. -/
theorem solenoidal_mollified_product_identity {u : SpatialField} {g : Fin 3 → SpatialField}
    (hu : MemLp u 2 volume) (hg : ∀ j, MemLp (g j) 2 volume)
    (hderiv : ∀ j, HasWeakSpatialDerivative j u (g j)) (hs : IsSolenoidal u)
    {φ : Space → ℝ} (hφ : IsSpatialTest φ) (i : Fin 3) (n : ℕ) :
    (∑ j : Fin 3, ∫ x, spatialTestDerivative j φ x * u x j *
      SobolevEmbedding.mollification (SobolevEmbedding.shrinkingMollifier n) u x i) =
    -(∑ j : Fin 3, ∫ x, φ x * u x j *
      SobolevEmbedding.mollification (SobolevEmbedding.shrinkingMollifier n) (g j) x i) := by
  let ρ := SobolevEmbedding.shrinkingMollifier n
  let v := SobolevEmbedding.mollification ρ u
  have hv : ContDiff ℝ ∞ v := SobolevEmbedding.mollification_smooth ρ u hu
  have hid := hs.identity (fun x => φ x * v x i) (spatialTest_mul_coordinate hφ hv i)
  have hd (j : Fin 3) (x : Space) :
      spatialTestDerivative j (fun y => φ y * v y i) x =
        spatialTestDerivative j φ x * v x i + φ x * SobolevEmbedding.mollification ρ (g j) x i := by
    rw [spatialTestDerivative_mul_coordinate hφ hv i j x]
    rw [show fderiv ℝ v x (coordinateVector j) =
      SobolevEmbedding.mollification ρ (g j) x from
        SobolevEmbedding.mollification_derivative (hderiv j) hu ρ x]
  have hleft (j : Fin 3) : Integrable (fun x => spatialTestDerivative j φ x * u x j * v x i) :=
    weighted_product_integrable hu (SobolevEmbedding.mollification_memLp ρ u hu)
      ((hφ.derivative j).memLp ⊤) j i
  have hright (j : Fin 3) : Integrable
      (fun x => φ x * u x j * SobolevEmbedding.mollification ρ (g j) x i) :=
    weighted_product_integrable hu (SobolevEmbedding.mollification_memLp ρ (g j) (hg j))
      (hφ.memLp ⊤) j i
  have hex : (fun x => ∑ j : Fin 3, u x j * spatialTestDerivative j (fun y => φ y * v y i) x) =
      fun x => (∑ j : Fin 3, spatialTestDerivative j φ x * u x j * v x i) +
        ∑ j : Fin 3, φ x * u x j * SobolevEmbedding.mollification ρ (g j) x i := by
    funext x
    simp only [hd, mul_add, Finset.sum_add_distrib]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;> ring
  rw [hex, integral_add (integrable_finsetSum _ (fun j _ => hleft j))
    (integrable_finsetSum _ (fun j _ => hright j)),
    integral_finsetSum _ (fun j _ => hleft j), integral_finsetSum _ (fun j _ => hright j)] at hid
  exact eq_neg_of_add_eq_zero_left hid

/-- The genuine H¹ solenoidal product rule, stated against every compact smooth
spatial test. It has no smoothness or density premise on the velocity. -/
theorem solenoidal_weak_product_identity {u : SpatialField} {g : Fin 3 → SpatialField}
    (hu : MemLp u 2 volume) (hg : ∀ j, MemLp (g j) 2 volume)
    (hderiv : ∀ j, HasWeakSpatialDerivative j u (g j)) (hs : IsSolenoidal u)
    {φ : Space → ℝ} (hφ : IsSpatialTest φ) (i : Fin 3) :
    (∑ j : Fin 3, ∫ x, spatialTestDerivative j φ x * u x j * u x i) =
      -(∑ j : Fin 3, ∫ x, φ x * u x j * g j x i) := by
  have hl := tendsto_finsetSum Finset.univ (fun j _ =>
    weighted_product_mollification_tendsto hu hu ((hφ.derivative j).memLp ⊤) j i)
  have hr := (tendsto_finsetSum Finset.univ (fun j _ =>
    weighted_product_mollification_tendsto hu (hg j) (hφ.memLp ⊤) j i)).neg
  apply tendsto_nhds_unique hl
  have he (n : ℕ) := solenoidal_mollified_product_identity hu hg hderiv hs hφ i n
  exact hr.congr' (Eventually.of_forall (fun n => (he n).symm))

/-- The convection term paired with a compact smooth scalar test is genuinely integrable. -/
theorem convection_test_integrable {u : SpatialField} {g : Fin 3 → SpatialField}
    (hu : MemLp u 2 volume) (hg : ∀ j, MemLp (g j) 2 volume)
    {φ : Space → ℝ} (hφ : IsSpatialTest φ) (i : Fin 3) :
    Integrable (fun x => φ x * ∑ j : Fin 3, u x j * g j x i) volume := by
  have h := integrable_finsetSum Finset.univ (fun j _ =>
    weighted_product_integrable hu (hg j) (hφ.memLp ⊤) j i)
  simpa only [Finset.mul_sum, mul_assoc] using h

/-- Distributional divergence of the quadratic stress is the actual convection
term. This is the scalar integral formulation used by pressure reconstruction. -/
theorem solenoidal_convection_test_identity {u : SpatialField} {g : Fin 3 → SpatialField}
    (hu : MemLp u 2 volume) (hg : ∀ j, MemLp (g j) 2 volume)
    (hderiv : ∀ j, HasWeakSpatialDerivative j u (g j)) (hs : IsSolenoidal u)
    {φ : Space → ℝ} (hφ : IsSpatialTest φ) (i : Fin 3) :
    (∫ x, φ x * ∑ j : Fin 3, u x j * g j x i) =
      -(∑ j : Fin 3, ∫ x, spatialTestDerivative j φ x * u x j * u x i) := by
  have he : (∫ x, φ x * ∑ j : Fin 3, u x j * g j x i) =
      ∑ j : Fin 3, ∫ x, φ x * u x j * g j x i := by
    simp_rw [Finset.mul_sum, ← mul_assoc]
    exact integral_finsetSum _ (fun j _ =>
      weighted_product_integrable hu (hg j) (hφ.memLp ⊤) j i)
  rw [he]
  linarith [solenoidal_weak_product_identity hu hg hderiv hs hφ i]

/-- The actual convection field has precisely the weak divergence of the
quadratic velocity stress. -/
theorem velocityForcing_test_identity {u : SpatialField} {g : Fin 3 → SpatialField}
    (hu : MemLp u 2 volume) (hg : ∀ j, MemLp (g j) 2 volume)
    (hderiv : ∀ j, HasWeakSpatialDerivative j u (g j)) (hs : IsSolenoidal u)
    {φ : Space → ℝ} (hφ : IsSpatialTest φ) (i : Fin 3) :
    (∫ x, φ x * velocityForcing u g i x) =
      -(∑ j : Fin 3, ∫ x, spatialTestDerivative j φ x * u x j * u x i) :=
  solenoidal_convection_test_identity hu hg hderiv hs hφ i

/-- A second distributional divergence identifies the source in the pressure
Poisson equation with the genuine double divergence of the quadratic stress. -/
theorem velocityForcing_divergence_test_identity {u : SpatialField}
    {g : Fin 3 → SpatialField}
    (hu : MemLp u 2 volume) (hg : ∀ j, MemLp (g j) 2 volume)
    (hderiv : ∀ j, HasWeakSpatialDerivative j u (g j)) (hs : IsSolenoidal u)
    {φ : Space → ℝ} (hφ : IsSpatialTest φ) :
    (∑ i : Fin 3, ∫ x, spatialTestDerivative i φ x * velocityForcing u g i x) =
      -(∑ i : Fin 3, ∑ j : Fin 3,
        ∫ x, spatialTestDerivative j (spatialTestDerivative i φ) x * u x j * u x i) := by
  calc
    _ = ∑ i : Fin 3, -(∑ j : Fin 3,
        ∫ x, spatialTestDerivative j (spatialTestDerivative i φ) x * u x j * u x i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact velocityForcing_test_identity hu hg hderiv hs (hφ.derivative i) i
    _ = _ := by rw [Finset.sum_neg_distrib]

end UnforcedLeray.PressureAnalysis

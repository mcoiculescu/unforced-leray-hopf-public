import UnforcedLeray.Lib.HeatCylinder.WeakOutput
import UnforcedLeray.Lib.HeatCylinder.BochnerPath
import UnforcedLeray.Lib.TrainB.VecBridge
import UnforcedLeray.Lib.CylinderB.Space

/-!
# Actual Gaussian heat output in the train's cylinder Sobolev graph

This packages the Gaussian-tailed heatDiv output with its genuine weak derivatives. The carrier
is the train's Euclidean vector space; the kernel estimates remain on B0284's product plane and
are transferred through the explicit coordinate CLM and cell-measure identities.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Train (Vec)

/-- The actual `Vec`-valued derivative fields used to represent Gaussian heatDiv in H³. -/
noncomputable def heatDivH3Field {c θ : ℝ} (T : Plane → Plane × Plane)
    (α : UnforcedLeray.Sob.Idx 2 3) (z : Plane) : Vec :=
  UnforcedLeray.Train.toVec
    (UnforcedLeray.B0296.heatDiv θ
      (UnforcedLeray.Sob.iterD ((UnforcedLeray.Sob.cylinder c).word α) T) z)

private theorem heatDivH3_measure_eq_cell (c : ℝ) :
    UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) = UnforcedLeray.Cyl.cellμ c := by
  rw [UnforcedLeray.Cyl.wμ_ρwW]
  simp [UnforcedLeray.Cyl.wμ]

/-- Each actual Gaussian derivative field belongs to the unweighted H³ cell measure. -/
theorem memLp_heatDivH3Field {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {T : Plane → Plane × Plane} (hT : UnforcedLeray.Sob.IsCylSmooth c T)
    (α : UnforcedLeray.Sob.Idx 2 3) :
    MemLp (heatDivH3Field (c := c) (θ := θ) T α) 2
      (UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))) := by
  rw [heatDivH3_measure_eq_cell]
  let vs := (UnforcedLeray.Sob.cylinder c).word α
  have hplane := memLp_iterD_heatDiv_of_cylSmooth hc hθ hT vs
  have hcomm := iterD_heatDiv_commute hc hθ hT vs
  have hheatPlane : MemLp (UnforcedLeray.B0296.heatDiv θ
      (UnforcedLeray.Sob.iterD vs T)) 2 (UnforcedLeray.B0284.cellMeasure c) := by
    apply (memLp_congr_ae (Filter.Eventually.of_forall fun z => congrFun hcomm z)).mp
    exact hplane
  have hvecNorm : MemLp (fun z => UnforcedLeray.Train.toVec
      (UnforcedLeray.B0296.heatDiv θ (UnforcedLeray.Sob.iterD vs T) z)) 2
      (UnforcedLeray.B0284.cellMeasure c) :=
    (UnforcedLeray.Train.toVecL : Plane →L[ℝ] Vec).comp_memLp' hheatPlane
  have hderiv : UnforcedLeray.Sob.IsCylSmooth c (UnforcedLeray.Sob.iterD vs T) :=
    hT.iterD vs
  have hperPlane : UnforcedLeray.B0284.IsQPeriodic c
      (UnforcedLeray.B0296.heatDiv θ (UnforcedLeray.Sob.iterD vs T)) := by
    have hinput : UnforcedLeray.B0284.IsQPeriodic c (UnforcedLeray.Sob.iterD vs T) := by
      intro z
      have hcoord : (z.1 + c, z.2) = z + (c, 0) := by ext <;> simp
      rw [hcoord]
      exact hderiv.periodic z
    exact UnforcedLeray.B0296.heatDiv_periodic (θ := θ) hinput
  have hperVec : UnforcedLeray.B0284.IsQPeriodic c
      (fun z => UnforcedLeray.Train.toVec
        (UnforcedLeray.B0296.heatDiv θ (UnforcedLeray.Sob.iterD vs T) z)) := by
    intro z
    exact congrArg UnforcedLeray.Train.toVec (hperPlane z)
  have hmeasVec : Measurable (fun z => UnforcedLeray.Train.toVec
      (UnforcedLeray.B0296.heatDiv θ (UnforcedLeray.Sob.iterD vs T) z)) := by
    have hcont := (UnforcedLeray.Train.toVecL : Plane →L[ℝ] Vec).continuous.comp
      (differentiable_heatDiv_of_cylSmooth hc hθ hderiv).continuous
    exact hcont.measurable
  exact memLp_cyl_of_memLp_cellMeasure hc hmeasVec hperVec hvecNorm

/-- Per-derivative `L²` smoothing for the actual Gaussian H³ field. The period normalization
cancels between the input and output, leaving only the explicit Gaussian and coordinate factors.
-/
theorem eLpNorm_heatDivH3Field_le {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {T : Plane → Plane × Plane} (hT : UnforcedLeray.Sob.IsCylSmooth c T)
    (α : UnforcedLeray.Sob.Idx 2 3) :
    eLpNorm (heatDivH3Field (c := c) (θ := θ) T α) 2 (UnforcedLeray.Cyl.cellμ c) ≤
      (ENNReal.ofReal ‖(UnforcedLeray.Train.toVecL : Plane →L[ℝ] Vec)‖ *
        ENNReal.ofReal (heatDivL2Coeff θ)) *
        eLpNorm (UnforcedLeray.Sob.iterD ((UnforcedLeray.Sob.cylinder c).word α) T)
          2 (UnforcedLeray.Cyl.cellμ c) := by
  let vs := (UnforcedLeray.Sob.cylinder c).word α
  have hderiv : UnforcedLeray.Sob.IsCylSmooth c (UnforcedLeray.Sob.iterD vs T) :=
    hT.iterD vs
  have hinputMeas : Measurable (UnforcedLeray.Sob.iterD vs T) :=
    hderiv.smooth.continuous.measurable
  have hinputPer : UnforcedLeray.B0284.IsQPeriodic c (UnforcedLeray.Sob.iterD vs T) := by
    intro z
    have hcoord : (z.1 + c, z.2) = z + (c, 0) := by ext <;> simp
    rw [hcoord]
    exact hderiv.periodic z
  have hheat := UnforcedLeray.HeatCylinder.heatDiv_L2_smoothing hc hθ hinputPer
    hinputMeas.aestronglyMeasurable
  have hheatCoeff : eLpNorm (UnforcedLeray.B0296.heatDiv θ
      (UnforcedLeray.Sob.iterD vs T)) 2 (UnforcedLeray.B0284.cellMeasure c) ≤
      ENNReal.ofReal (heatDivL2Coeff θ) *
        eLpNorm (UnforcedLeray.Sob.iterD vs T) 2
          (UnforcedLeray.B0284.cellMeasure c) := by
    simpa [heatDivL2Coeff] using hheat
  have hplaneOutPer : UnforcedLeray.B0284.IsQPeriodic c
      (UnforcedLeray.B0296.heatDiv θ (UnforcedLeray.Sob.iterD vs T)) :=
    UnforcedLeray.B0296.heatDiv_periodic (θ := θ) hinputPer
  have hvecPer : UnforcedLeray.B0284.IsQPeriodic c
      (heatDivH3Field (c := c) (θ := θ) T α) := by
    intro z
    exact congrArg UnforcedLeray.Train.toVec (hplaneOutPer z)
  have hvecMeas : Measurable (heatDivH3Field (c := c) (θ := θ) T α) := by
    have hcont := (UnforcedLeray.Train.toVecL : Plane →L[ℝ] Vec).continuous.comp
      (differentiable_heatDiv_of_cylSmooth hc hθ hderiv).continuous
    exact hcont.measurable
  have hvecNorm : eLpNorm (heatDivH3Field (c := c) (θ := θ) T α) 2
      (UnforcedLeray.B0284.cellMeasure c) ≤
      ENNReal.ofReal ‖(UnforcedLeray.Train.toVecL : Plane →L[ℝ] Vec)‖ *
        eLpNorm (UnforcedLeray.B0296.heatDiv θ (UnforcedLeray.Sob.iterD vs T)) 2
          (UnforcedLeray.B0284.cellMeasure c) := by
    change eLpNorm (fun z => UnforcedLeray.Train.toVec
      (UnforcedLeray.B0296.heatDiv θ (UnforcedLeray.Sob.iterD vs T) z)) 2
        (UnforcedLeray.B0284.cellMeasure c) ≤ _
    exact UnforcedLeray.TrainB.eLpNorm_vecFieldOfPlane_le
      (c := c) (p := 2) (u := fun z =>
        UnforcedLeray.B0296.heatDiv θ (UnforcedLeray.Sob.iterD vs T) z)
  have hnormNormalized : eLpNorm (heatDivH3Field (c := c) (θ := θ) T α) 2
      (UnforcedLeray.B0284.cellMeasure c) ≤
      (ENNReal.ofReal ‖(UnforcedLeray.Train.toVecL : Plane →L[ℝ] Vec)‖ *
        ENNReal.ofReal (heatDivL2Coeff θ)) *
        eLpNorm (UnforcedLeray.Sob.iterD vs T) 2 (UnforcedLeray.B0284.cellMeasure c) := by
    calc
      eLpNorm (heatDivH3Field (c := c) (θ := θ) T α) 2
          (UnforcedLeray.B0284.cellMeasure c) ≤
          ENNReal.ofReal ‖(UnforcedLeray.Train.toVecL : Plane →L[ℝ] Vec)‖ *
            eLpNorm (UnforcedLeray.B0296.heatDiv θ (UnforcedLeray.Sob.iterD vs T)) 2
              (UnforcedLeray.B0284.cellMeasure c) := hvecNorm
      _ ≤ ENNReal.ofReal ‖(UnforcedLeray.Train.toVecL : Plane →L[ℝ] Vec)‖ *
          (ENNReal.ofReal (heatDivL2Coeff θ) * eLpNorm
            (UnforcedLeray.Sob.iterD vs T) 2 (UnforcedLeray.B0284.cellMeasure c)) := by
          gcongr
      _ = (ENNReal.ofReal ‖(UnforcedLeray.Train.toVecL : Plane →L[ℝ] Vec)‖ *
          ENNReal.ofReal (heatDivL2Coeff θ)) *
          eLpNorm (UnforcedLeray.Sob.iterD vs T) 2 (UnforcedLeray.B0284.cellMeasure c) := by
          ac_rfl
  have hOutSq := eLpNorm_sq_cyl_eq_cellMeasure hc hvecMeas hvecPer
  have hInSq := eLpNorm_sq_cyl_eq_cellMeasure hc hinputMeas hinputPer
  let K := ENNReal.ofReal ‖(UnforcedLeray.Train.toVecL : Plane →L[ℝ] Vec)‖ *
    ENNReal.ofReal (heatDivL2Coeff θ)
  have hsq : (eLpNorm (heatDivH3Field (c := c) (θ := θ) T α) 2
      (UnforcedLeray.Cyl.cellμ c)) ^ 2 ≤
      (K * eLpNorm (UnforcedLeray.Sob.iterD vs T) 2
        (UnforcedLeray.Cyl.cellμ c)) ^ 2 := by
    calc
      (eLpNorm (heatDivH3Field (c := c) (θ := θ) T α) 2
          (UnforcedLeray.Cyl.cellμ c)) ^ 2 =
          ENNReal.ofReal c *
            (eLpNorm (heatDivH3Field (c := c) (θ := θ) T α) 2
              (UnforcedLeray.B0284.cellMeasure c)) ^ 2 := hOutSq
      _ ≤ ENNReal.ofReal c *
          (K * eLpNorm (UnforcedLeray.Sob.iterD vs T) 2
            (UnforcedLeray.B0284.cellMeasure c)) ^ 2 := by
          gcongr
      _ = (K * eLpNorm (UnforcedLeray.Sob.iterD vs T) 2
            (UnforcedLeray.Cyl.cellμ c)) ^ 2 := by
          rw [mul_pow]
          calc
            ENNReal.ofReal c * (K ^ 2 *
                eLpNorm (UnforcedLeray.Sob.iterD vs T) 2
                  (UnforcedLeray.B0284.cellMeasure c) ^ 2) =
                K ^ 2 * (ENNReal.ofReal c *
                  eLpNorm (UnforcedLeray.Sob.iterD vs T) 2
                    (UnforcedLeray.B0284.cellMeasure c) ^ 2) := by ac_rfl
            _ = K ^ 2 * (eLpNorm (UnforcedLeray.Sob.iterD vs T) 2
                (UnforcedLeray.Cyl.cellμ c)) ^ 2 := by rw [← hInSq]
            _ = (K * eLpNorm (UnforcedLeray.Sob.iterD vs T) 2
                (UnforcedLeray.Cyl.cellμ c)) ^ 2 := by
                  simp [mul_pow, K]
  exact (ENNReal.pow_le_pow_left_iff two_ne_zero).1 hsq

/-- Summing the per-derivative estimates gives a squared derivative-energy bound for the whole
finite H³ index family. This is the aggregate `L²` estimate before rewriting the sum as the
`W.ofFields` graph norm. -/
theorem sum_eLpNorm_sq_heatDivH3Field_le {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {T : Plane → Plane × Plane} (hT : UnforcedLeray.Sob.IsCylSmooth c T) :
    ∑ α : UnforcedLeray.Sob.Idx 2 3,
        (eLpNorm (heatDivH3Field (c := c) (θ := θ) T α) 2
          (UnforcedLeray.Cyl.cellμ c)) ^ 2 ≤
      (ENNReal.ofReal ‖(UnforcedLeray.Train.toVecL : Plane →L[ℝ] Vec)‖ *
        ENNReal.ofReal (heatDivL2Coeff θ)) ^ 2 *
        ∑ α : UnforcedLeray.Sob.Idx 2 3,
          (eLpNorm (UnforcedLeray.Sob.iterD
            ((UnforcedLeray.Sob.cylinder c).word α) T) 2
            (UnforcedLeray.Cyl.cellμ c)) ^ 2 := by
  let K := ENNReal.ofReal ‖(UnforcedLeray.Train.toVecL : Plane →L[ℝ] Vec)‖ *
    ENNReal.ofReal (heatDivL2Coeff θ)
  calc
    ∑ α : UnforcedLeray.Sob.Idx 2 3,
        (eLpNorm (heatDivH3Field (c := c) (θ := θ) T α) 2
          (UnforcedLeray.Cyl.cellμ c)) ^ 2 ≤
      ∑ α : UnforcedLeray.Sob.Idx 2 3,
        (K * eLpNorm (UnforcedLeray.Sob.iterD
          ((UnforcedLeray.Sob.cylinder c).word α) T) 2
          (UnforcedLeray.Cyl.cellμ c)) ^ 2 := by
      apply Finset.sum_le_sum
      intro α _
      exact (ENNReal.pow_le_pow_left_iff two_ne_zero).2
        (eLpNorm_heatDivH3Field_le hc hθ hT α)
    _ = ∑ α : UnforcedLeray.Sob.Idx 2 3,
          K ^ 2 * (eLpNorm (UnforcedLeray.Sob.iterD
            ((UnforcedLeray.Sob.cylinder c).word α) T) 2
            (UnforcedLeray.Cyl.cellμ c)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro α _
      rw [mul_pow]
    _ = K ^ 2 * ∑ α : UnforcedLeray.Sob.Idx 2 3,
          (eLpNorm (UnforcedLeray.Sob.iterD
            ((UnforcedLeray.Sob.cylinder c).word α) T) 2
            (UnforcedLeray.Cyl.cellμ c)) ^ 2 := by
      rw [← Finset.mul_sum]

/-- The genuine weak derivative identities for the H³ field component family. -/
theorem hasWeakDeriv_heatDivH3Field {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {T : Plane → Plane × Plane} (hT : UnforcedLeray.Sob.IsCylSmooth c T)
    (α : UnforcedLeray.Sob.Idx 2 3) :
    UnforcedLeray.Sob.HasWeakDeriv (UnforcedLeray.Sob.cylinder c)
      ((UnforcedLeray.Sob.cylinder c).word α)
      (heatDivH3Field (c := c) (θ := θ) T UnforcedLeray.Sob.Idx.zero)
      (heatDivH3Field (c := c) (θ := θ) T α) := by
  let vs := (UnforcedLeray.Sob.cylinder c).word α
  have hweak := hasWeakDeriv_iterD_heatDiv hc hθ hT vs
  have hvec := hweak.map_clm (UnforcedLeray.Train.toVecL : Plane →L[ℝ] Vec)
  have hbase : (fun z => UnforcedLeray.Train.toVec
      (UnforcedLeray.B0296.heatDiv θ T z)) =ᵐ[(UnforcedLeray.Sob.cylinder c).μ]
      heatDivH3Field (c := c) (θ := θ) T UnforcedLeray.Sob.Idx.zero := by
    filter_upwards [] with z
    simp [heatDivH3Field, UnforcedLeray.Sob.iterD_nil]
  have hderiv : (fun z => UnforcedLeray.Train.toVec
      (UnforcedLeray.Sob.iterD vs (UnforcedLeray.B0296.heatDiv θ T) z)) =ᵐ[
        (UnforcedLeray.Sob.cylinder c).μ]
      heatDivH3Field (c := c) (θ := θ) T α := by
    filter_upwards [] with z
    dsimp [heatDivH3Field]
    rw [iterD_heatDiv_commute hc hθ hT vs]
  exact hvec.congr_ae hbase hderiv

/-- The actual B0296 Gaussian heatDiv of a smooth periodic compact-axial tensor lies in the
train's centered-cell `H³` Sobolev graph after conversion to Euclidean train vectors. The
components are the actual convolution of each input derivative; no compact-support claim is made
for the heat output. -/
noncomputable def heatDivH3 {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {T : Plane → Plane × Plane} (hT : UnforcedLeray.Sob.IsCylSmooth c T) :
    UnforcedLeray.Cyl.H ℝ Vec c 0 3 :=
  UnforcedLeray.Sob.W.ofFields (heatDivH3Field (c := c) (θ := θ) T)
    (memLp_heatDivH3Field hc hθ hT) (hasWeakDeriv_heatDivH3Field hc hθ hT)

/-- The actual H³ graph norm of `heatDivH3` is the square root of the finite sum of centered-cell
derivative L² energies represented by `heatDivH3Field`. -/
theorem heatDivH3_norm_sq_eq {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {T : Plane → Plane × Plane} (hT : UnforcedLeray.Sob.IsCylSmooth c T) :
    ‖heatDivH3 hc hθ hT‖ ^ 2 =
      ∑ α : UnforcedLeray.Sob.Idx 2 3,
        (ENNReal.toReal (eLpNorm (heatDivH3Field (c := c) (θ := θ) T α) 2
          (UnforcedLeray.Cyl.cellμ c))) ^ 2 := by
  rw [heatDivH3, UnforcedLeray.Sob.W.norm_sq]
  simp_rw [UnforcedLeray.Sob.W.deriv_ofFields, Lp.norm_toLp,
    heatDivH3_measure_eq_cell]

/-- Quantitative H³ graph norm bound for actual cylinder heatDiv on smooth periodic
compact-axial tensors. The coefficient is the explicit Gaussian smoothing factor times the
product-plane to Euclidean-vector coordinate conversion norm. -/
theorem norm_heatDivH3_le_energy {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {T : Plane → Plane × Plane} (hT : UnforcedLeray.Sob.IsCylSmooth c T) :
    ‖heatDivH3 hc hθ hT‖ ^ 2 ≤
      ((ENNReal.ofReal ‖(UnforcedLeray.Train.toVecL : Plane →L[ℝ] Vec)‖ *
        ENNReal.ofReal (heatDivL2Coeff θ)).toReal) ^ 2 *
        ∑ α : UnforcedLeray.Sob.Idx 2 3,
          (eLpNorm (UnforcedLeray.Sob.iterD
            ((UnforcedLeray.Sob.cylinder c).word α) T) 2
            (UnforcedLeray.Cyl.cellμ c)).toReal ^ 2 := by
  let K : ℝ≥0∞ := ENNReal.ofReal ‖(UnforcedLeray.Train.toVecL : Plane →L[ℝ] Vec)‖ *
    ENNReal.ofReal (heatDivL2Coeff θ)
  have hinputMem (α : UnforcedLeray.Sob.Idx 2 3) :
      MemLp (UnforcedLeray.Sob.iterD ((UnforcedLeray.Sob.cylinder c).word α) T) 2
        (UnforcedLeray.Cyl.cellμ c) := by
    let vs := (UnforcedLeray.Sob.cylinder c).word α
    have hderiv : UnforcedLeray.Sob.IsCylSmooth c (UnforcedLeray.Sob.iterD vs T) :=
      hT.iterD vs
    have hmeas := hderiv.smooth.continuous.measurable
    have hper : UnforcedLeray.B0284.IsQPeriodic c (UnforcedLeray.Sob.iterD vs T) := by
      intro z
      have hcoord : (z.1 + c, z.2) = z + (c, 0) := by ext <;> simp
      rw [hcoord]
      exact hderiv.periodic z
    exact memLp_cyl_of_memLp_cellMeasure hc hmeas hper
      (memLp_tensor_iterD_cylSmooth_normalized hc hT vs)
  have houtputMem (α : UnforcedLeray.Sob.Idx 2 3) :
      MemLp (heatDivH3Field (c := c) (θ := θ) T α) 2
        (UnforcedLeray.Cyl.cellμ c) := by
    have h := memLp_heatDivH3Field hc hθ hT α
    rwa [heatDivH3_measure_eq_cell] at h
  have hsum := sum_eLpNorm_sq_heatDivH3Field_le hc hθ hT
  have hsumInputTop :
      (∑ α : UnforcedLeray.Sob.Idx 2 3,
        (eLpNorm (UnforcedLeray.Sob.iterD
          ((UnforcedLeray.Sob.cylinder c).word α) T) 2
          (UnforcedLeray.Cyl.cellμ c)) ^ 2) < ⊤ := by
    apply ENNReal.sum_lt_top.mpr
    intro α _
    exact ENNReal.pow_lt_top (hinputMem α).eLpNorm_ne_top.lt_top
  have hsumOutputTop :
      (∑ α : UnforcedLeray.Sob.Idx 2 3,
        (eLpNorm (heatDivH3Field (c := c) (θ := θ) T α) 2
          (UnforcedLeray.Cyl.cellμ c)) ^ 2) < ⊤ := by
    apply ENNReal.sum_lt_top.mpr
    intro α _
    exact ENNReal.pow_lt_top (houtputMem α).eLpNorm_ne_top.lt_top
  have hKtop : K < ⊤ := by
    dsimp [K]
    exact ENNReal.mul_lt_top ENNReal.ofReal_ne_top.lt_top ENNReal.ofReal_ne_top.lt_top
  have hRhsTop : K ^ 2 * (∑ α : UnforcedLeray.Sob.Idx 2 3,
      (eLpNorm (UnforcedLeray.Sob.iterD
        ((UnforcedLeray.Sob.cylinder c).word α) T) 2
        (UnforcedLeray.Cyl.cellμ c)) ^ 2) < ⊤ := by
    exact ENNReal.mul_lt_top (ENNReal.pow_lt_top hKtop) hsumInputTop
  have hreal : ENNReal.toReal (∑ α : UnforcedLeray.Sob.Idx 2 3,
      (eLpNorm (heatDivH3Field (c := c) (θ := θ) T α) 2
        (UnforcedLeray.Cyl.cellμ c)) ^ 2) ≤
      ENNReal.toReal (K ^ 2 * ∑ α : UnforcedLeray.Sob.Idx 2 3,
        (eLpNorm (UnforcedLeray.Sob.iterD
          ((UnforcedLeray.Sob.cylinder c).word α) T) 2
          (UnforcedLeray.Cyl.cellμ c)) ^ 2) :=
    ENNReal.toReal_mono hRhsTop.ne hsum
  rw [heatDivH3_norm_sq_eq hc hθ hT]
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow] at hreal
  rw [ENNReal.toReal_sum (fun α _ => (ENNReal.pow_lt_top
      (houtputMem α).eLpNorm_ne_top.lt_top).ne)] at hreal
  rw [ENNReal.toReal_sum (fun α _ => (ENNReal.pow_lt_top
      (hinputMem α).eLpNorm_ne_top.lt_top).ne)] at hreal
  simp_rw [ENNReal.toReal_pow] at hreal
  simpa [K, ENNReal.toReal_pow] using hreal

/-- The value of the constructed H³ element is the actual Gaussian heatDiv output. -/
theorem heatDivH3_value_ae {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {T : Plane → Plane × Plane} (hT : UnforcedLeray.Sob.IsCylSmooth c T) :
    (⇑(UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2
      (heatDivH3 hc hθ hT)) : Plane → Vec) =ᵐ[
        UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
          (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))]
      (fun z => UnforcedLeray.Train.toVec (UnforcedLeray.B0296.heatDiv θ T z)) := by
  rw [heatDivH3, UnforcedLeray.Sob.W.value_ofFields]
  have hmem := memLp_heatDivH3Field hc hθ hT UnforcedLeray.Sob.Idx.zero
  filter_upwards [hmem.coeFn_toLp] with z hz
  simpa [heatDivH3Field, UnforcedLeray.Cyl.word_zero,
    UnforcedLeray.Sob.iterD_nil] using hz

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.heatDivH3
#print axioms UnforcedLeray.HeatCylinder.memLp_heatDivH3Field
#print axioms UnforcedLeray.HeatCylinder.eLpNorm_heatDivH3Field_le
#print axioms UnforcedLeray.HeatCylinder.sum_eLpNorm_sq_heatDivH3Field_le
#print axioms UnforcedLeray.HeatCylinder.heatDivH3_norm_sq_eq
#print axioms UnforcedLeray.HeatCylinder.hasWeakDeriv_heatDivH3Field
#print axioms UnforcedLeray.HeatCylinder.heatDivH3_value_ae
#print axioms UnforcedLeray.HeatCylinder.norm_heatDivH3_le_energy

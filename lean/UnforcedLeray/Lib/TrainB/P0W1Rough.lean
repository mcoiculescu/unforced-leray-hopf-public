import UnforcedLeray.Lib.TrainB.P0W1MeasurePreserving
import UnforcedLeray.Lib.TrainB.P0StrongQuotient
import UnforcedLeray.Lib.TrainB.P0Horizontal
import UnforcedLeray.Lib.TrainB.P0Translation

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology
open UnforcedLeray.Cyl

namespace UnforcedLeray.TrainB

private theorem qShiftField_isCylSmooth {c h : ℝ} {u : Plane → Vec2}
    (hu : Sob.IsCylSmooth c u) : Sob.IsCylSmooth c (qShiftField h u) := by
  obtain ⟨R, hR⟩ := hu.bounded
  refine ⟨hu.smooth.comp (contDiff_id.add contDiff_const), ?_, ⟨R, ?_⟩⟩
  · intro z
    change u ((z + ((c, 0) : Plane)) + ((h, 0) : Plane)) = u (z + ((h, 0) : Plane))
    have heq : (z + ((c, 0) : Plane)) + ((h, 0) : Plane) =
        (z + ((h, 0) : Plane)) + ((c, 0) : Plane) := by ext <;> simp <;> ring
    rw [heq]
    exact hu.periodic _
  · intro z hz
    exact hR (z + ((h, 0) : Plane)) (by simpa using hz)

private theorem etaShiftField_isCylSmooth {c h : ℝ} {u : Plane → Vec2}
    (hu : Sob.IsCylSmooth c u) : Sob.IsCylSmooth c (etaShiftField h u) := by
  obtain ⟨R, hR⟩ := hu.bounded
  refine ⟨hu.smooth.comp (contDiff_id.add contDiff_const), ?_, ⟨R + |h|, ?_⟩⟩
  · intro z
    change u ((z + ((c, 0) : Plane)) + ((0, h) : Plane)) = u (z + ((0, h) : Plane))
    calc
      u ((z + ((c, 0) : Plane)) + ((0, h) : Plane)) =
          u ((z + ((0, h) : Plane)) + ((c, 0) : Plane)) := by congr 1 <;> ext <;> simp [add_assoc, add_comm]
      _ = u (z + ((0, h) : Plane)) := hu.periodic _
  · intro z hz
    have htriangle : |z.2| ≤ |z.2 + h| + |h| := by
      calc
        |z.2| = |(z.2 + h) + (-h)| := by congr 1 <;> ring
        _ ≤ |z.2 + h| + |-h| := abs_add_le _ _
        _ = |z.2 + h| + |h| := by rw [abs_neg]
    have hz' : R < |z.2 + h| := by linarith
    exact hR (z + ((0 : ℝ), h)) (by simpa using hz')

/-- A horizontal smooth shift difference has a genuine centered-cell L² representative. -/
private theorem qShiftSubMemLp {c h : ℝ} {u : Plane → Vec2}
    (hu : Sob.IsCylSmooth c u) : MemLp (fun z => qShiftField h u z - u z) 2 (cellμ c) := by
  have h1 : MemLp (qShiftField h u) 2 (cellμ c) := by
    rw [← vecH1_measure_eq_cell c]
    exact (qShiftField_isCylSmooth hu).memLp (Cyl.ρwW c ^ (0 : ℝ)) 2
  have h2 : MemLp u 2 (cellμ c) := by
    rw [← vecH1_measure_eq_cell c]
    exact hu.memLp (Cyl.ρwW c ^ (0 : ℝ)) 2
  exact h1.sub h2

/-- An axial smooth shift difference has a genuine centered-cell L² representative. -/
private theorem etaShiftSubMemLp {c h : ℝ} {u : Plane → Vec2}
    (hu : Sob.IsCylSmooth c u) : MemLp (fun z => etaShiftField h u z - u z) 2 (cellμ c) := by
  have h1 : MemLp (etaShiftField h u) 2 (cellμ c) := by
    rw [← vecH1_measure_eq_cell c]
    exact (etaShiftField_isCylSmooth hu).memLp (Cyl.ρwW c ^ (0 : ℝ)) 2
  have h2 : MemLp u 2 (cellμ c) := by
    rw [← vecH1_measure_eq_cell c]
    exact hu.memLp (Cyl.ρwW c ^ (0 : ℝ)) 2
  exact h1.sub h2

/-- On a smooth `VecH1` representative, the horizontal cell-L² translation modulus is the
classical FTC estimate, expressed using the representative-transparent maps. -/
theorem norm_qShift_sub_le_ofCylSmooth {c h : ℝ} (hc : 0 < c)
    {u : Plane → Vec2} (hu : Sob.IsCylSmooth c u) :
    ‖qShiftL2 hc h (vecH1ValueCellCLM_MP
        (Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ))
          (𝕜 := ℝ) (F := Vec2) (k := 1) (p := 2) hc u hu)) -
      vecH1ValueCellCLM_MP (Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ))
        (𝕜 := ℝ) (F := Vec2) (k := 1) (p := 2) hc u hu)‖ ≤
      |h| * ‖vecH1DqCellCLM_MP (Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ))
        (𝕜 := ℝ) (F := Vec2) (k := 1) (p := 2) hc u hu)‖ := by
  let x : VecH1 c := Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ))
    (𝕜 := ℝ) (F := Vec2) (k := 1) (p := 2) hc u hu
  let hm := qShiftSubMemLp (h := h) hu
  have hdiff : (qShiftL2 hc h (vecH1ValueCellCLM_MP x) -
      vecH1ValueCellCLM_MP x : L2v c) =
      (hm.toLp (fun z => qShiftField h u z - u z)) := by
    apply Lp.ext
    have hs := qShiftL2_ae_periodic (a := h) hc (vecH1ValueCellCLM_MP x)
      (fun z => by
        have hz : z + ((c, 0) : Plane) = (z.1 + c, z.2) := by ext <;> simp
        rw [← hz]
        exact hu.periodic z)
      (vecH1ValueCellCLM_MP_ofCylSmooth_ae hc hu)
    have hv := vecH1ValueCellCLM_MP_ofCylSmooth_ae hc hu
    have hsub := Lp.coeFn_sub (qShiftL2 hc h (vecH1ValueCellCLM_MP x))
      (vecH1ValueCellCLM_MP x)
    filter_upwards [hs, hv, hm.coeFn_toLp, hsub] with z hzS hzV hzM hzSub
    calc
      ((qShiftL2 hc h (vecH1ValueCellCLM_MP x) - vecH1ValueCellCLM_MP x :
        L2v c) : Plane → Vec2) z =
          ((qShiftL2 hc h (vecH1ValueCellCLM_MP x) : Plane → Vec2) z -
            (vecH1ValueCellCLM_MP x : Plane → Vec2) z) := hzSub
      _ = qShiftField h u z - u z := by rw [hzS, hzV]
      _ = (hm.toLp (fun z => qShiftField h u z - u z) : Plane → Vec2) z := hzM.symm
  have hpartMem : MemLp (Cyl.partialQ u) 2 (cellμ c) := by
    rw [← vecH1_measure_eq_cell c]
    have heq : (fun z => fderiv ℝ u z ((1 : ℝ), (0 : ℝ))) = Cyl.partialQ u :=
      funext (fun z => (Cyl.partialQ_eq_fderiv
        (hu.smooth.differentiable (by simp)) z).symm)
    rw [← heq]
    exact (hu.dir ((1 : ℝ), (0 : ℝ))).memLp (Cyl.ρwW c ^ (0 : ℝ)) 2
  have hnormShift : ‖qShiftL2 hc h (vecH1ValueCellCLM_MP x) -
      vecH1ValueCellCLM_MP x‖ = (eLpNorm (fun z => qShiftField h u z - u z)
        2 (cellμ c)).toReal := by
    rw [hdiff, Lp.norm_toLp]
  have hnormDeriv : ‖vecH1DqCellCLM_MP x‖ =
      (eLpNorm (Cyl.partialQ u) 2 (cellμ c)).toReal := by
    rw [Lp.norm_def]
    exact congrArg ENNReal.toReal (eLpNorm_congr_ae
      (vecH1DqCellCLM_MP_ofCylSmooth_ae hc hu))
  have hle := eLpNorm_qShift_sub_le_of_cylSmooth (c := c) (h := h) hc hu
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hpartMem.2.ne) hle
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg h)] at hreal
  calc
    ‖qShiftL2 hc h (vecH1ValueCellCLM_MP x) - vecH1ValueCellCLM_MP x‖ =
        (eLpNorm (fun z => qShiftField h u z - u z) 2 (cellμ c)).toReal := hnormShift
    _ ≤ |h| * (eLpNorm (Cyl.partialQ u) 2 (cellμ c)).toReal := hreal
    _ = |h| * ‖vecH1DqCellCLM_MP x‖ := by rw [hnormDeriv]

/-- On a smooth `VecH1` representative, the axial cell-L² translation modulus is the classical
FTC estimate, expressed using the representative-transparent maps. -/
theorem norm_etaShift_sub_le_ofCylSmooth {c h : ℝ} (hc : 0 < c)
    {u : Plane → Vec2} (hu : Sob.IsCylSmooth c u) :
    ‖etaShiftL2 c h (vecH1ValueCellCLM_MP
        (Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ))
          (𝕜 := ℝ) (F := Vec2) (k := 1) (p := 2) hc u hu)) -
      vecH1ValueCellCLM_MP (Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ))
        (𝕜 := ℝ) (F := Vec2) (k := 1) (p := 2) hc u hu)‖ ≤
      |h| * ‖vecH1DetaCellCLM_MP (Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ))
        (𝕜 := ℝ) (F := Vec2) (k := 1) (p := 2) hc u hu)‖ := by
  let x : VecH1 c := Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ))
    (𝕜 := ℝ) (F := Vec2) (k := 1) (p := 2) hc u hu
  let hm := etaShiftSubMemLp (h := h) hu
  have hdiff : (etaShiftL2 c h (vecH1ValueCellCLM_MP x) -
      vecH1ValueCellCLM_MP x : L2v c) =
      (hm.toLp (fun z => etaShiftField h u z - u z)) := by
    apply Lp.ext
    have hs := etaShiftL2_ae (c := c) (a := h) (vecH1ValueCellCLM_MP x)
    have hv := vecH1ValueCellCLM_MP_ofCylSmooth_ae hc hu
    have hsub := Lp.coeFn_sub (etaShiftL2 c h (vecH1ValueCellCLM_MP x))
      (vecH1ValueCellCLM_MP x)
    have hvShift := (measurePreserving_etaShift c h).quasiMeasurePreserving.ae hv
    filter_upwards [hs, hv, hvShift, hm.coeFn_toLp, hsub] with
      z hzS hzVOriginal hzV hzM hzSub
    have hzV' : (vecH1ValueCellCLM_MP x : Plane → Vec2) (z + ((0 : ℝ), h)) =
        u (z + ((0 : ℝ), h)) := by simpa [x] using hzV
    calc
      ((etaShiftL2 c h (vecH1ValueCellCLM_MP x) - vecH1ValueCellCLM_MP x :
        L2v c) : Plane → Vec2) z =
          ((etaShiftL2 c h (vecH1ValueCellCLM_MP x) : Plane → Vec2) z -
            (vecH1ValueCellCLM_MP x : Plane → Vec2) z) := hzSub
      _ = etaShiftField h u z - u z := by rw [hzS, hzV', hzVOriginal]; rfl
      _ = (hm.toLp (fun z => etaShiftField h u z - u z) : Plane → Vec2) z := hzM.symm
  have hpartMem : MemLp (Cyl.partialEta u) 2 (cellμ c) := by
    rw [← vecH1_measure_eq_cell c]
    have heq : (fun z => fderiv ℝ u z ((0 : ℝ), (1 : ℝ))) = Cyl.partialEta u :=
      funext (fun z => (Cyl.partialEta_eq_fderiv
        (hu.smooth.differentiable (by simp)) z).symm)
    rw [← heq]
    exact (hu.dir ((0 : ℝ), (1 : ℝ))).memLp (Cyl.ρwW c ^ (0 : ℝ)) 2
  have hnormShift : ‖etaShiftL2 c h (vecH1ValueCellCLM_MP x) -
      vecH1ValueCellCLM_MP x‖ = (eLpNorm (fun z => etaShiftField h u z - u z)
        2 (cellμ c)).toReal := by
    rw [hdiff, Lp.norm_toLp]
  have hnormDeriv : ‖vecH1DetaCellCLM_MP x‖ =
      (eLpNorm (Cyl.partialEta u) 2 (cellμ c)).toReal := by
    rw [Lp.norm_def]
    exact congrArg ENNReal.toReal (eLpNorm_congr_ae
      (vecH1DetaCellCLM_MP_ofCylSmooth_ae hc hu))
  have hle := eLpNorm_etaShift_sub_le_of_cylSmooth (c := c) (h := h) hc hu
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hpartMem.2.ne) hle
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg h)] at hreal
  calc
    ‖etaShiftL2 c h (vecH1ValueCellCLM_MP x) - vecH1ValueCellCLM_MP x‖ =
        (eLpNorm (fun z => etaShiftField h u z - u z) 2 (cellμ c)).toReal := hnormShift
    _ ≤ |h| * (eLpNorm (Cyl.partialEta u) 2 (cellμ c)).toReal := hreal
    _ = |h| * ‖vecH1DetaCellCLM_MP x‖ := by rw [hnormDeriv]

/-- Every actual VecH1 class has the horizontal cell-L² translation modulus, by smooth density
and continuity of its value and weak derivative projections. -/
theorem norm_qShift_sub_le_of_vecH1 {c h : ℝ} (hc : 0 < c) (x : VecH1 c) :
    ‖qShiftL2 hc h (vecH1ValueCellCLM_MP x) - vecH1ValueCellCLM_MP x‖ ≤
      |h| * ‖vecH1DqCellCLM_MP x‖ := by
  obtain ⟨y, f, hf, hy, hlim⟩ := exists_smoothVecH1_sequence hc x
  let Q : VecH1 c →L[ℝ] L2v c :=
    (qShiftL2Isometry hc h).toContinuousLinearMap.comp vecH1ValueCellCLM_MP -
      vecH1ValueCellCLM_MP
  have hQlim : Tendsto (fun n => Q (y n)) atTop (𝓝 (Q x)) :=
    Q.continuous.tendsto x |>.comp hlim
  have hDlim : Tendsto (fun n => vecH1DqCellCLM_MP (y n)) atTop
      (𝓝 (vecH1DqCellCLM_MP x)) :=
    vecH1DqCellCLM_MP.continuous.tendsto x |>.comp hlim
  have hnormQ : Tendsto (fun n => ‖Q (y n)‖) atTop (𝓝 ‖Q x‖) :=
    (continuous_norm.tendsto (Q x)).comp hQlim
  have hnormD : Tendsto (fun n => ‖vecH1DqCellCLM_MP (y n)‖) atTop
      (𝓝 ‖vecH1DqCellCLM_MP x‖) :=
    (continuous_norm.tendsto (vecH1DqCellCLM_MP x)).comp hDlim
  have hnormD' : Tendsto (fun n => |h| * ‖vecH1DqCellCLM_MP (y n)‖) atTop
      (𝓝 (|h| * ‖vecH1DqCellCLM_MP x‖)) := by
    simpa using (tendsto_const_nhds.mul hnormD)
  have hbound : ∀ n, ‖Q (y n)‖ ≤ |h| * ‖vecH1DqCellCLM_MP (y n)‖ := by
    intro n
    have hs := norm_qShift_sub_le_ofCylSmooth (c := c) (h := h) hc (hf n)
    simpa [Q, qShiftL2Isometry, qShiftL2Linear, hy n] using hs
  have hlimBound := le_of_tendsto_of_tendsto hnormQ hnormD'
    (Eventually.of_forall hbound)
  simpa [Q, qShiftL2Isometry, qShiftL2Linear] using hlimBound

/-- Every actual VecH1 class has the axial cell-L² translation modulus, by smooth density and
continuity of its value and weak derivative projections. -/
theorem norm_etaShift_sub_le_of_vecH1 {c h : ℝ} (hc : 0 < c) (x : VecH1 c) :
    ‖etaShiftL2 c h (vecH1ValueCellCLM_MP x) - vecH1ValueCellCLM_MP x‖ ≤
      |h| * ‖vecH1DetaCellCLM_MP x‖ := by
  obtain ⟨y, f, hf, hy, hlim⟩ := exists_smoothVecH1_sequence hc x
  let Q : VecH1 c →L[ℝ] L2v c :=
    (etaShiftL2 c h).toContinuousLinearMap.comp vecH1ValueCellCLM_MP -
      vecH1ValueCellCLM_MP
  have hQlim : Tendsto (fun n => Q (y n)) atTop (𝓝 (Q x)) :=
    Q.continuous.tendsto x |>.comp hlim
  have hDlim : Tendsto (fun n => vecH1DetaCellCLM_MP (y n)) atTop
      (𝓝 (vecH1DetaCellCLM_MP x)) :=
    vecH1DetaCellCLM_MP.continuous.tendsto x |>.comp hlim
  have hnormQ : Tendsto (fun n => ‖Q (y n)‖) atTop (𝓝 ‖Q x‖) :=
    (continuous_norm.tendsto (Q x)).comp hQlim
  have hnormD : Tendsto (fun n => ‖vecH1DetaCellCLM_MP (y n)‖) atTop
      (𝓝 ‖vecH1DetaCellCLM_MP x‖) :=
    (continuous_norm.tendsto (vecH1DetaCellCLM_MP x)).comp hDlim
  have hnormD' : Tendsto (fun n => |h| * ‖vecH1DetaCellCLM_MP (y n)‖) atTop
      (𝓝 (|h| * ‖vecH1DetaCellCLM_MP x‖)) := by
    simpa using (tendsto_const_nhds.mul hnormD)
  have hbound : ∀ n, ‖Q (y n)‖ ≤ |h| * ‖vecH1DetaCellCLM_MP (y n)‖ := by
    intro n
    have hs := norm_etaShift_sub_le_ofCylSmooth (c := c) (h := h) hc (hf n)
    simpa [Q, hy n] using hs
  have hlimBound := le_of_tendsto_of_tendsto hnormQ hnormD'
    (Eventually.of_forall hbound)
  simpa [Q] using hlimBound

/-- The normalized horizontal translation quotient as a continuous operator on cell L². -/
noncomputable def qDifferenceQuotientCLM {c : ℝ} (hc : 0 < c) (h : ℝ) :
    L2v c →L[ℝ] L2v c :=
  h⁻¹ • ((qShiftL2Isometry hc h).toContinuousLinearMap -
    ContinuousLinearMap.id ℝ (L2v c))

/-- The normalized axial translation quotient as a continuous operator on cell L². -/
noncomputable def etaDifferenceQuotientCLM {c : ℝ} (h : ℝ) :
    L2v c →L[ℝ] L2v c :=
  h⁻¹ • ((etaShiftL2 c h).toContinuousLinearMap -
    ContinuousLinearMap.id ℝ (L2v c))

/-- For a smooth W¹ class, the actual horizontal quotient error in L² is exactly the smooth
pointwise error. -/
theorem qDifferenceQuotientCLM_error_norm_eq_ofCylSmooth {c h : ℝ} (hc : 0 < c)
    {u : Plane → Vec2} (hu : Sob.IsCylSmooth c u) :
    ‖qDifferenceQuotientCLM hc h
        (vecH1ValueCellCLM_MP (Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ))
          (𝕜 := ℝ) (F := Vec2) (k := 1) (p := 2) hc u hu)) -
      vecH1DqCellCLM_MP (Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ))
        (𝕜 := ℝ) (F := Vec2) (k := 1) (p := 2) hc u hu)‖ =
      (eLpNorm (fun z => h⁻¹ • (qShiftField h u z - u z) - Cyl.partialQ u z)
        2 (cellμ c)).toReal := by
  let x : VecH1 c := Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ))
    (𝕜 := ℝ) (F := Vec2) (k := 1) (p := 2) hc u hu
  let raw : L2v c := qShiftL2 hc h (vecH1ValueCellCLM_MP x) - vecH1ValueCellCLM_MP x
  have hraw : (raw : Plane → Vec2) =ᵐ[cellμ c]
      (fun z => qShiftField h u z - u z) := by
    have hs := qShiftL2_ae_periodic (a := h) hc (vecH1ValueCellCLM_MP x)
      (fun z => by
        have hz : z + ((c, 0) : Plane) = (z.1 + c, z.2) := by ext <;> simp
        rw [← hz]
        exact hu.periodic z)
      (vecH1ValueCellCLM_MP_ofCylSmooth_ae hc hu)
    have hv := vecH1ValueCellCLM_MP_ofCylSmooth_ae hc hu
    filter_upwards [Lp.coeFn_sub (qShiftL2 hc h (vecH1ValueCellCLM_MP x))
      (vecH1ValueCellCLM_MP x), hs, hv] with z hsub hzS hzV
    calc
      (raw : Plane → Vec2) z =
          ((qShiftL2 hc h (vecH1ValueCellCLM_MP x) : L2v c) : Plane → Vec2) z -
            ((vecH1ValueCellCLM_MP x : L2v c) : Plane → Vec2) z := hsub
      _ = qShiftField h u z - u z := by rw [hzS, hzV]
  have hsm : (h⁻¹ • raw : L2v c) =ᵐ[cellμ c]
      (fun z => h⁻¹ • (qShiftField h u z - u z)) := by
    filter_upwards [Lp.coeFn_smul (h⁻¹ : ℝ) raw, hraw] with z hsm hrawz
    calc
      ((h⁻¹ • raw : L2v c) : Plane → Vec2) z =
          (h⁻¹ • (raw : Plane → Vec2) z) := hsm
      _ = h⁻¹ • (qShiftField h u z - u z) := by rw [hrawz]
  have hderiv := vecH1DqCellCLM_MP_ofCylSmooth_ae hc hu
  have herr : (qDifferenceQuotientCLM hc h
      (vecH1ValueCellCLM_MP x) - vecH1DqCellCLM_MP x : L2v c) =ᵐ[cellμ c]
      (fun z => h⁻¹ • (qShiftField h u z - u z) - Cyl.partialQ u z) := by
    have hq : qDifferenceQuotientCLM hc h (vecH1ValueCellCLM_MP x) = h⁻¹ • raw := by
      simp [qDifferenceQuotientCLM, raw, qShiftL2Isometry, qShiftL2Linear,
        ContinuousLinearMap.id_apply]
    rw [hq]
    filter_upwards [Lp.coeFn_sub (h⁻¹ • raw) (vecH1DqCellCLM_MP x), hsm, hderiv]
      with z hsub hsmz hD
    calc
      ((h⁻¹ • raw - vecH1DqCellCLM_MP x : L2v c) : Plane → Vec2) z =
          ((h⁻¹ • raw : L2v c) : Plane → Vec2) z -
            ((vecH1DqCellCLM_MP x : L2v c) : Plane → Vec2) z := hsub
      _ = h⁻¹ • (qShiftField h u z - u z) - Cyl.partialQ u z := by rw [hsmz, hD]
  rw [Lp.norm_def]
  exact congrArg ENNReal.toReal (eLpNorm_congr_ae herr)

/-- For a smooth W¹ class, the actual axial quotient error in L² is exactly the smooth
pointwise error. -/
theorem etaDifferenceQuotientCLM_error_norm_eq_ofCylSmooth {c h : ℝ} (hc : 0 < c)
    {u : Plane → Vec2} (hu : Sob.IsCylSmooth c u) :
    ‖etaDifferenceQuotientCLM h
        (vecH1ValueCellCLM_MP (Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ))
          (𝕜 := ℝ) (F := Vec2) (k := 1) (p := 2) hc u hu)) -
      vecH1DetaCellCLM_MP (Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ))
        (𝕜 := ℝ) (F := Vec2) (k := 1) (p := 2) hc u hu)‖ =
      (eLpNorm (fun z => h⁻¹ • (etaShiftField h u z - u z) - Cyl.partialEta u z)
        2 (cellμ c)).toReal := by
  let x : VecH1 c := Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ))
    (𝕜 := ℝ) (F := Vec2) (k := 1) (p := 2) hc u hu
  let raw : L2v c := etaShiftL2 c h (vecH1ValueCellCLM_MP x) - vecH1ValueCellCLM_MP x
  have hraw : (raw : Plane → Vec2) =ᵐ[cellμ c]
      (fun z => etaShiftField h u z - u z) := by
    have hs := etaShiftL2_ae (c := c) (a := h) (vecH1ValueCellCLM_MP x)
    have hv := vecH1ValueCellCLM_MP_ofCylSmooth_ae hc hu
    have hvShift := (measurePreserving_etaShift c h).quasiMeasurePreserving.ae hv
    filter_upwards [Lp.coeFn_sub (etaShiftL2 c h (vecH1ValueCellCLM_MP x))
      (vecH1ValueCellCLM_MP x), hs, hv, hvShift] with z hsub hzS hzV hzVShift
    have hzV' : (vecH1ValueCellCLM_MP x : Plane → Vec2) (z + ((0 : ℝ), h)) =
        u (z + ((0 : ℝ), h)) := by simpa [x] using hzVShift
    have hzV0 : (vecH1ValueCellCLM_MP x : Plane → Vec2) z = u z := by
      simpa [x] using hzV
    calc
      (raw : Plane → Vec2) z =
          ((etaShiftL2 c h (vecH1ValueCellCLM_MP x) : L2v c) : Plane → Vec2) z -
            ((vecH1ValueCellCLM_MP x : L2v c) : Plane → Vec2) z := hsub
      _ = etaShiftField h u z - u z := by rw [hzS, hzV', hzV0]; rfl
  have hsm : (h⁻¹ • raw : L2v c) =ᵐ[cellμ c]
      (fun z => h⁻¹ • (etaShiftField h u z - u z)) := by
    filter_upwards [Lp.coeFn_smul (h⁻¹ : ℝ) raw, hraw] with z hsm hrawz
    calc
      ((h⁻¹ • raw : L2v c) : Plane → Vec2) z =
          (h⁻¹ • (raw : Plane → Vec2) z) := hsm
      _ = h⁻¹ • (etaShiftField h u z - u z) := by rw [hrawz]
  have hderiv := vecH1DetaCellCLM_MP_ofCylSmooth_ae hc hu
  have herr : (etaDifferenceQuotientCLM h
      (vecH1ValueCellCLM_MP x) - vecH1DetaCellCLM_MP x : L2v c) =ᵐ[cellμ c]
      (fun z => h⁻¹ • (etaShiftField h u z - u z) - Cyl.partialEta u z) := by
    have hq : etaDifferenceQuotientCLM h (vecH1ValueCellCLM_MP x) = h⁻¹ • raw := by
      simp [etaDifferenceQuotientCLM, raw, ContinuousLinearMap.id_apply]
    rw [hq]
    filter_upwards [Lp.coeFn_sub (h⁻¹ • raw) (vecH1DetaCellCLM_MP x), hsm, hderiv]
      with z hsub hsmz hD
    calc
      ((h⁻¹ • raw - vecH1DetaCellCLM_MP x : L2v c) : Plane → Vec2) z =
          ((h⁻¹ • raw : L2v c) : Plane → Vec2) z -
            ((vecH1DetaCellCLM_MP x : L2v c) : Plane → Vec2) z := hsub
      _ = h⁻¹ • (etaShiftField h u z - u z) - Cyl.partialEta u z := by rw [hsmz, hD]
  rw [Lp.norm_def]
  exact congrArg ENNReal.toReal (eLpNorm_congr_ae herr)

/-- Smooth normalized horizontal quotients converge strongly to the actual weak derivative in
the centered-cell L² carrier. -/
theorem tendsto_qDifferenceQuotientCLM_error_zero_ofCylSmooth {c : ℝ} (hc : 0 < c)
    {u : Plane → Vec2} (hu : Sob.IsCylSmooth c u) :
    Tendsto (fun h => ‖qDifferenceQuotientCLM hc h
      (vecH1ValueCellCLM_MP (Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ))
        (𝕜 := ℝ) (F := Vec2) (k := 1) (p := 2) hc u hu)) -
      vecH1DqCellCLM_MP (Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ))
        (𝕜 := ℝ) (F := Vec2) (k := 1) (p := 2) hc u hu)‖)
      (nhdsWithin 0 {h : ℝ | h ≠ 0}) (𝓝 0) := by
  have he := tendsto_eLpNorm_qDifferenceQuotient_error_zero hc hu
  have hr := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp he
  have heq : (fun h => ‖qDifferenceQuotientCLM hc h
      (vecH1ValueCellCLM_MP (Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ))
        (𝕜 := ℝ) (F := Vec2) (k := 1) (p := 2) hc u hu)) -
      vecH1DqCellCLM_MP (Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ))
        (𝕜 := ℝ) (F := Vec2) (k := 1) (p := 2) hc u hu)‖) =
      fun h => (eLpNorm (fun z => h⁻¹ • (qShiftField h u z - u z) - Cyl.partialQ u z)
        2 (cellμ c)).toReal := by
    funext h
    exact qDifferenceQuotientCLM_error_norm_eq_ofCylSmooth (c := c) (h := h) hc hu
  rw [heq]
  simpa [Function.comp_def] using hr

/-- Smooth normalized axial quotients converge strongly to the actual weak derivative in the
centered-cell L² carrier. -/
theorem tendsto_etaDifferenceQuotientCLM_error_zero_ofCylSmooth {c : ℝ} (hc : 0 < c)
    {u : Plane → Vec2} (hu : Sob.IsCylSmooth c u) :
    Tendsto (fun h => ‖etaDifferenceQuotientCLM h
      (vecH1ValueCellCLM_MP (Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ))
        (𝕜 := ℝ) (F := Vec2) (k := 1) (p := 2) hc u hu)) -
      vecH1DetaCellCLM_MP (Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ))
        (𝕜 := ℝ) (F := Vec2) (k := 1) (p := 2) hc u hu)‖)
      (nhdsWithin 0 {h : ℝ | h ≠ 0}) (𝓝 0) := by
  have he := tendsto_eLpNorm_etaDifferenceQuotient_error_zero hc hu
  have hr := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp he
  have heq : (fun h => ‖etaDifferenceQuotientCLM h
      (vecH1ValueCellCLM_MP (Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ))
        (𝕜 := ℝ) (F := Vec2) (k := 1) (p := 2) hc u hu)) -
      vecH1DetaCellCLM_MP (Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ))
        (𝕜 := ℝ) (F := Vec2) (k := 1) (p := 2) hc u hu)‖) =
      fun h => (eLpNorm (fun z => h⁻¹ • (etaShiftField h u z - u z) - Cyl.partialEta u z)
        2 (cellμ c)).toReal := by
    funext h
    exact etaDifferenceQuotientCLM_error_norm_eq_ofCylSmooth (c := c) (h := h) hc hu
  rw [heq]
  simpa [Function.comp_def] using hr

/-- For nonzero horizontal increments, replacing a VecH1 input by a smooth approximation changes
the quotient error by at most twice the weak-derivative approximation error. -/
theorem norm_qDifferenceQuotientCLM_error_le_of_vecH1 {c h : ℝ} (hc : 0 < c)
    (hh : h ≠ 0) (x y : VecH1 c) :
    ‖qDifferenceQuotientCLM hc h (vecH1ValueCellCLM_MP x) -
        vecH1DqCellCLM_MP x‖ ≤
      2 * ‖vecH1DqCellCLM_MP (x - y)‖ +
        ‖qDifferenceQuotientCLM hc h (vecH1ValueCellCLM_MP y) -
          vecH1DqCellCLM_MP y‖ := by
  have hquotient (z : VecH1 c) :
      ‖qDifferenceQuotientCLM hc h (vecH1ValueCellCLM_MP z)‖ ≤
        ‖vecH1DqCellCLM_MP z‖ := by
    have hmod := norm_qShift_sub_le_of_vecH1 (h := h) hc z
    have habs : |h⁻¹| * |h| = 1 := by
      rw [abs_inv]
      exact inv_mul_cancel₀ (abs_ne_zero.mpr hh)
    have heq : ‖qDifferenceQuotientCLM hc h (vecH1ValueCellCLM_MP z)‖ =
        |h⁻¹| * ‖qShiftL2 hc h (vecH1ValueCellCLM_MP z) -
          vecH1ValueCellCLM_MP z‖ := by
      simp [qDifferenceQuotientCLM, qShiftL2Isometry, qShiftL2Linear,
        norm_smul, Real.norm_eq_abs]
    rw [heq]
    calc
      |h⁻¹| * ‖qShiftL2 hc h (vecH1ValueCellCLM_MP z) -
          vecH1ValueCellCLM_MP z‖ ≤
        |h⁻¹| * (|h| * ‖vecH1DqCellCLM_MP z‖) :=
          mul_le_mul_of_nonneg_left hmod (abs_nonneg _)
      _ = ‖vecH1DqCellCLM_MP z‖ := by rw [← mul_assoc, habs, one_mul]
  let E : VecH1 c →L[ℝ] L2v c :=
    (qDifferenceQuotientCLM hc h).comp vecH1ValueCellCLM_MP -
      vecH1DqCellCLM_MP
  have hsplit : E x = E (x - y) + E y := by
    calc
      E x = (E x - E y) + E y := by rw [sub_add_cancel]
      _ = E (x - y) + E y := by rw [map_sub]
  have hsmall : ∀ z : VecH1 c, ‖E z‖ ≤ 2 * ‖vecH1DqCellCLM_MP z‖ := by
    intro z
    have hE : E z = qDifferenceQuotientCLM hc h (vecH1ValueCellCLM_MP z) -
        vecH1DqCellCLM_MP z := by simp [E]
    rw [hE]
    calc
      ‖qDifferenceQuotientCLM hc h (vecH1ValueCellCLM_MP z) -
          vecH1DqCellCLM_MP z‖ ≤
        ‖qDifferenceQuotientCLM hc h (vecH1ValueCellCLM_MP z)‖ +
          ‖vecH1DqCellCLM_MP z‖ := norm_sub_le _ _
      _ ≤ 2 * ‖vecH1DqCellCLM_MP z‖ := by
        calc
          _ ≤ ‖vecH1DqCellCLM_MP z‖ + ‖vecH1DqCellCLM_MP z‖ :=
            add_le_add (hquotient z) (le_refl _)
          _ = 2 * ‖vecH1DqCellCLM_MP z‖ := by ring
  have hEx : E x = qDifferenceQuotientCLM hc h (vecH1ValueCellCLM_MP x) -
      vecH1DqCellCLM_MP x := by simp [E]
  have hEy : E y = qDifferenceQuotientCLM hc h (vecH1ValueCellCLM_MP y) -
      vecH1DqCellCLM_MP y := by simp [E]
  rw [← hEx, hsplit, hEy]
  calc
    ‖E (x - y) + E y‖ ≤ ‖E (x - y)‖ + ‖E y‖ := norm_add_le _ _
    _ ≤ 2 * ‖vecH1DqCellCLM_MP (x - y)‖ +
        ‖qDifferenceQuotientCLM hc h (vecH1ValueCellCLM_MP y) -
          vecH1DqCellCLM_MP y‖ := by
        rw [hEy] at *
        exact add_le_add (hsmall (x - y)) le_rfl

/-- The actual normalized horizontal translation quotients converge strongly to the weak
horizontal derivative for every VecH1 class. -/
theorem tendsto_qDifferenceQuotientCLM_error_zero_of_vecH1 {c : ℝ} (hc : 0 < c)
    (x : VecH1 c) :
    Tendsto (fun h => ‖qDifferenceQuotientCLM hc h
      (vecH1ValueCellCLM_MP x) - vecH1DqCellCLM_MP x‖)
      (nhdsWithin 0 {h : ℝ | h ≠ 0}) (𝓝 0) := by
  obtain ⟨y, f, hf, hy, hlim⟩ := exists_smoothVecH1_sequence hc x
  have hDlim : Tendsto (fun n => vecH1DqCellCLM_MP (y n)) atTop
      (𝓝 (vecH1DqCellCLM_MP x)) :=
    vecH1DqCellCLM_MP.continuous.tendsto x |>.comp hlim
  have hD0 : Tendsto (fun n => ‖vecH1DqCellCLM_MP (y n) -
      vecH1DqCellCLM_MP x‖) atTop (𝓝 0) := by
    have h := (tendsto_iff_norm_sub_tendsto_zero).mp hDlim
    simpa using h
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hDdist : ∀ᶠ n : ℕ in atTop,
      ‖vecH1DqCellCLM_MP (y n) - vecH1DqCellCLM_MP x‖ < ε / 8 := by
    simpa using (Metric.tendsto_nhds.mp hD0 (ε / 8) (by positivity))
  obtain ⟨n, hn⟩ := hDdist.exists
  have hSmooth := tendsto_qDifferenceQuotientCLM_error_zero_ofCylSmooth hc (hf n)
  have hSmooth' : Tendsto (fun h => ‖qDifferenceQuotientCLM hc h
      (vecH1ValueCellCLM_MP (y n)) - vecH1DqCellCLM_MP (y n)‖)
      (nhdsWithin 0 {h : ℝ | h ≠ 0}) (𝓝 0) := by
    simpa [hy n] using hSmooth
  have hSmoothEvent := Metric.tendsto_nhds.mp hSmooth' (ε / 2) (by positivity)
  filter_upwards [hSmoothEvent, self_mem_nhdsWithin] with h hErr hh
  have hrough := norm_qDifferenceQuotientCLM_error_le_of_vecH1 hc hh x (y n)
  have hErrNorm : ‖qDifferenceQuotientCLM hc h (vecH1ValueCellCLM_MP (y n)) -
      vecH1DqCellCLM_MP (y n)‖ < ε / 2 := by simpa using hErr
  have hDapprox : ‖vecH1DqCellCLM_MP (x - y n)‖ < ε / 8 := by
    simpa [map_sub, norm_sub_rev] using hn
  calc
    dist ‖qDifferenceQuotientCLM hc h (vecH1ValueCellCLM_MP x) -
      vecH1DqCellCLM_MP x‖ 0 =
        ‖qDifferenceQuotientCLM hc h (vecH1ValueCellCLM_MP x) -
          vecH1DqCellCLM_MP x‖ := by simp
    _ ≤ 2 * ‖vecH1DqCellCLM_MP (x - y n)‖ +
        ‖qDifferenceQuotientCLM hc h (vecH1ValueCellCLM_MP (y n)) -
          vecH1DqCellCLM_MP (y n)‖ := hrough
    _ < ε := by nlinarith [hDapprox, hErrNorm]

/-- The axial version of the nonzero-increment quotient approximation estimate. -/
theorem norm_etaDifferenceQuotientCLM_error_le_of_vecH1 {c h : ℝ} (hc : 0 < c)
    (hh : h ≠ 0) (x y : VecH1 c) :
    ‖etaDifferenceQuotientCLM h (vecH1ValueCellCLM_MP x) -
        vecH1DetaCellCLM_MP x‖ ≤
      2 * ‖vecH1DetaCellCLM_MP (x - y)‖ +
        ‖etaDifferenceQuotientCLM h (vecH1ValueCellCLM_MP y) -
          vecH1DetaCellCLM_MP y‖ := by
  have hquotient (z : VecH1 c) :
      ‖etaDifferenceQuotientCLM h (vecH1ValueCellCLM_MP z)‖ ≤
        ‖vecH1DetaCellCLM_MP z‖ := by
    have hmod := norm_etaShift_sub_le_of_vecH1 (h := h) hc z
    have habs : |h⁻¹| * |h| = 1 := by
      rw [abs_inv]
      exact inv_mul_cancel₀ (abs_ne_zero.mpr hh)
    have heq : ‖etaDifferenceQuotientCLM h (vecH1ValueCellCLM_MP z)‖ =
        |h⁻¹| * ‖etaShiftL2 c h (vecH1ValueCellCLM_MP z) -
          vecH1ValueCellCLM_MP z‖ := by
      simp [etaDifferenceQuotientCLM, norm_smul, Real.norm_eq_abs]
    rw [heq]
    calc
      |h⁻¹| * ‖etaShiftL2 c h (vecH1ValueCellCLM_MP z) -
          vecH1ValueCellCLM_MP z‖ ≤
        |h⁻¹| * (|h| * ‖vecH1DetaCellCLM_MP z‖) :=
          mul_le_mul_of_nonneg_left hmod (abs_nonneg _)
      _ = ‖vecH1DetaCellCLM_MP z‖ := by rw [← mul_assoc, habs, one_mul]
  let E : VecH1 c →L[ℝ] L2v c :=
    (etaDifferenceQuotientCLM h).comp vecH1ValueCellCLM_MP -
      vecH1DetaCellCLM_MP
  have hsplit : E x = E (x - y) + E y := by
    calc
      E x = (E x - E y) + E y := by rw [sub_add_cancel]
      _ = E (x - y) + E y := by rw [map_sub]
  have hsmall : ∀ z : VecH1 c, ‖E z‖ ≤ 2 * ‖vecH1DetaCellCLM_MP z‖ := by
    intro z
    have hE : E z = etaDifferenceQuotientCLM h (vecH1ValueCellCLM_MP z) -
        vecH1DetaCellCLM_MP z := by simp [E]
    rw [hE]
    calc
      ‖etaDifferenceQuotientCLM h (vecH1ValueCellCLM_MP z) -
          vecH1DetaCellCLM_MP z‖ ≤
        ‖etaDifferenceQuotientCLM h (vecH1ValueCellCLM_MP z)‖ +
          ‖vecH1DetaCellCLM_MP z‖ := norm_sub_le _ _
      _ ≤ 2 * ‖vecH1DetaCellCLM_MP z‖ := by
        calc
          _ ≤ ‖vecH1DetaCellCLM_MP z‖ + ‖vecH1DetaCellCLM_MP z‖ :=
            add_le_add (hquotient z) (le_refl _)
          _ = 2 * ‖vecH1DetaCellCLM_MP z‖ := by ring
  have hEx : E x = etaDifferenceQuotientCLM h (vecH1ValueCellCLM_MP x) -
      vecH1DetaCellCLM_MP x := by simp [E]
  have hEy : E y = etaDifferenceQuotientCLM h (vecH1ValueCellCLM_MP y) -
      vecH1DetaCellCLM_MP y := by simp [E]
  rw [← hEx, hsplit, hEy]
  calc
    ‖E (x - y) + E y‖ ≤ ‖E (x - y)‖ + ‖E y‖ := norm_add_le _ _
    _ ≤ 2 * ‖vecH1DetaCellCLM_MP (x - y)‖ +
        ‖etaDifferenceQuotientCLM h (vecH1ValueCellCLM_MP y) -
          vecH1DetaCellCLM_MP y‖ := by
        rw [hEy] at *
        exact add_le_add (hsmall (x - y)) le_rfl

/-- The actual normalized axial translation quotients converge strongly to the weak axial
derivative for every VecH1 class. -/
theorem tendsto_etaDifferenceQuotientCLM_error_zero_of_vecH1 {c : ℝ} (hc : 0 < c)
    (x : VecH1 c) :
    Tendsto (fun h => ‖etaDifferenceQuotientCLM h
      (vecH1ValueCellCLM_MP x) - vecH1DetaCellCLM_MP x‖)
      (nhdsWithin 0 {h : ℝ | h ≠ 0}) (𝓝 0) := by
  obtain ⟨y, f, hf, hy, hlim⟩ := exists_smoothVecH1_sequence hc x
  have hDlim : Tendsto (fun n => vecH1DetaCellCLM_MP (y n)) atTop
      (𝓝 (vecH1DetaCellCLM_MP x)) :=
    vecH1DetaCellCLM_MP.continuous.tendsto x |>.comp hlim
  have hD0 : Tendsto (fun n => ‖vecH1DetaCellCLM_MP (y n) -
      vecH1DetaCellCLM_MP x‖) atTop (𝓝 0) := by
    have h := (tendsto_iff_norm_sub_tendsto_zero).mp hDlim
    simpa using h
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hDdist : ∀ᶠ n : ℕ in atTop,
      ‖vecH1DetaCellCLM_MP (y n) - vecH1DetaCellCLM_MP x‖ < ε / 8 := by
    simpa using (Metric.tendsto_nhds.mp hD0 (ε / 8) (by positivity))
  obtain ⟨n, hn⟩ := hDdist.exists
  have hSmooth := tendsto_etaDifferenceQuotientCLM_error_zero_ofCylSmooth hc (hf n)
  have hSmooth' : Tendsto (fun h => ‖etaDifferenceQuotientCLM h
      (vecH1ValueCellCLM_MP (y n)) - vecH1DetaCellCLM_MP (y n)‖)
      (nhdsWithin 0 {h : ℝ | h ≠ 0}) (𝓝 0) := by
    simpa [hy n] using hSmooth
  have hSmoothEvent := Metric.tendsto_nhds.mp hSmooth' (ε / 2) (by positivity)
  filter_upwards [hSmoothEvent, self_mem_nhdsWithin] with h hErr hh
  have hrough := norm_etaDifferenceQuotientCLM_error_le_of_vecH1 hc hh x (y n)
  have hErrNorm : ‖etaDifferenceQuotientCLM h (vecH1ValueCellCLM_MP (y n)) -
      vecH1DetaCellCLM_MP (y n)‖ < ε / 2 := by simpa using hErr
  have hDapprox : ‖vecH1DetaCellCLM_MP (x - y n)‖ < ε / 8 := by
    simpa [map_sub, norm_sub_rev] using hn
  calc
    dist ‖etaDifferenceQuotientCLM h (vecH1ValueCellCLM_MP x) -
      vecH1DetaCellCLM_MP x‖ 0 =
        ‖etaDifferenceQuotientCLM h (vecH1ValueCellCLM_MP x) -
          vecH1DetaCellCLM_MP x‖ := by simp
    _ ≤ 2 * ‖vecH1DetaCellCLM_MP (x - y n)‖ +
        ‖etaDifferenceQuotientCLM h (vecH1ValueCellCLM_MP (y n)) -
          vecH1DetaCellCLM_MP (y n)‖ := hrough
    _ < ε := by nlinarith [hDapprox, hErrNorm]

end UnforcedLeray.TrainB

#print axioms UnforcedLeray.TrainB.norm_qShift_sub_le_ofCylSmooth
#print axioms UnforcedLeray.TrainB.norm_etaShift_sub_le_ofCylSmooth
#print axioms UnforcedLeray.TrainB.norm_qShift_sub_le_of_vecH1
#print axioms UnforcedLeray.TrainB.norm_etaShift_sub_le_of_vecH1
#print axioms UnforcedLeray.TrainB.qDifferenceQuotientCLM
#print axioms UnforcedLeray.TrainB.etaDifferenceQuotientCLM
#print axioms UnforcedLeray.TrainB.qDifferenceQuotientCLM_error_norm_eq_ofCylSmooth
#print axioms UnforcedLeray.TrainB.etaDifferenceQuotientCLM_error_norm_eq_ofCylSmooth
#print axioms UnforcedLeray.TrainB.tendsto_qDifferenceQuotientCLM_error_zero_ofCylSmooth
#print axioms UnforcedLeray.TrainB.tendsto_etaDifferenceQuotientCLM_error_zero_ofCylSmooth
#print axioms UnforcedLeray.TrainB.norm_qDifferenceQuotientCLM_error_le_of_vecH1
#print axioms UnforcedLeray.TrainB.tendsto_qDifferenceQuotientCLM_error_zero_of_vecH1
#print axioms UnforcedLeray.TrainB.norm_etaDifferenceQuotientCLM_error_le_of_vecH1
#print axioms UnforcedLeray.TrainB.tendsto_etaDifferenceQuotientCLM_error_zero_of_vecH1

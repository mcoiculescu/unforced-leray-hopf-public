import UnforcedLeray.Short.PartI.Sub.PartI_T08_4_1_1_1_2_2_1_3_2
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.EtaCutoffFacts
import UnforcedLeray.Short.PartI.Tasks.TrainCutoffEnergyProof.CellToolkit
import UnforcedLeray.Short.PartI.Tasks.TrainCutoffEnergyProof.SliceSmooth
import UnforcedLeray.Short.PartI.Tasks.TrainCutoffEnergyProof.PressureIdentity

/-!
# Part I, task `PartI:T08/4/1/1/1/2/2/1/3/2/6`: leaf `VelPressureIdentity`

Source of record: `the November 2 reference manuscript` lines 273-288.
Target: `velPressureIdentity_proof : VelPressureIdentity` (`Sub/PartI_T08_4_1_1_1_2_2_1_3_2.lean`).

Mathematics (single train, `π = p`, `w = v`, `div v = 0`). With `φ = etaCutoff R`, the fluxes
`G_q = φ p v₀` and `G_η = φ p v₁` satisfy, pointwise,
`∂_q G_q + ∂_η G_η = φ ⟨v, ∇p⟩ + φ' p v₁`, since `∂_q v₀ + ∂_η v₁ = 0`. Both fluxes are periodic
in `q` (resp. vanish for `|η| ≥ 2R`), so cell integration by parts (`CellDerivZero`) gives
`∫ φ ⟨v, ∇p⟩ = -∫ φ' p v₁`, i.e. `velCutoffPressure = velPressureRhs`.

The calculus helpers `prId_*` are taken from the compiled difference-energy model
`Tasks/TrainCutoffEnergyProof/PressureIdentity.lean` (they are generic in the functions); the flux
lemmas and the theorem are written for a single train.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

/-- The `q`-flux of the single-train pressure term: `G_q(z) = φ_R(z_η) p(z) v₀(z)`. -/
def vpIdGq {ν c : ℝ} (tr : B0140.TrainSol ν c) (R s : ℝ) (z : Plane) : ℝ :=
  etaCutoff R z.2 * tr.p s z * tr.v s z 0

/-- The `η`-flux of the single-train pressure term: `G_η(z) = φ_R(z_η) p(z) v₁(z)`. -/
def vpIdGe {ν c : ℝ} (tr : B0140.TrainSol ν c) (R s : ℝ) (z : Plane) : ℝ :=
  etaCutoff R z.2 * tr.p s z * tr.v s z 1

/-- `∂_q G_q` by the product rule (`φ` is independent of `q`). -/
theorem vpId_Gq_pQ {ν c : ℝ} (tr : B0140.TrainSol ν c) (R s : ℝ)
    (hP : Differentiable ℝ (tr.p s)) (hW : Differentiable ℝ (fun x => tr.v s x 0))
    (z : Plane) :
    Cyl.partialQ (vpIdGq tr R s) z =
      etaCutoff R z.2 * Cyl.partialQ (tr.p s) z * tr.v s z 0 +
        etaCutoff R z.2 * tr.p s z * Cyl.partialQ (fun x => tr.v s x 0) z := by
  have hd : HasDerivAt (fun q : ℝ => vpIdGq tr R s (q, z.2))
      (etaCutoff R z.2 * Cyl.partialQ (tr.p s) z * tr.v s z 0 +
        etaCutoff R z.2 * tr.p s z * Cyl.partialQ (fun x => tr.v s x 0) z) z.1 :=
    ((prId_line_q hP z).const_mul (etaCutoff R z.2)).mul (prId_line_q hW z)
  exact hd.deriv

/-- `∂_η G_η` by the product rule (`φ` depends on `η`). -/
theorem vpId_Ge_pE {ν c : ℝ} (tr : B0140.TrainSol ν c) (R s : ℝ)
    (hφ : Differentiable ℝ (etaCutoff R)) (hP : Differentiable ℝ (tr.p s))
    (hW : Differentiable ℝ (fun x => tr.v s x 1)) (z : Plane) :
    Cyl.partialEta (vpIdGe tr R s) z =
      (deriv (etaCutoff R) z.2 * tr.p s z +
          etaCutoff R z.2 * Cyl.partialEta (tr.p s) z) * tr.v s z 1 +
        etaCutoff R z.2 * tr.p s z * Cyl.partialEta (fun x => tr.v s x 1) z := by
  have hd : HasDerivAt (fun η : ℝ => vpIdGe tr R s (z.1, η))
      ((deriv (etaCutoff R) z.2 * tr.p s z +
          etaCutoff R z.2 * Cyl.partialEta (tr.p s) z) * tr.v s z 1 +
        etaCutoff R z.2 * tr.p s z * Cyl.partialEta (fun x => tr.v s x 1) z) z.2 :=
    (((hφ z.2).hasDerivAt).mul (prId_line_e hP z)).mul (prId_line_e hW z)
  exact hd.deriv

/-- **`PartI:T08/4/1/1/1/2/2/1/3/2/6`, target `VelPressureIdentity`.** -/
theorem velPressureIdentity_proof : UnforcedLeray.Short.PartI.VelPressureIdentity := by
  intro ν c hν hc tr R hR s hs0
  unfold velCutoffPressure velPressureRhs
  have hcut := etaCutoffFacts
  unfold EtaCutoffFacts at hcut
  obtain ⟨C₀, -, hcut⟩ := hcut
  obtain ⟨hφS, -, -, hφ0, hφd⟩ := hcut R hR
  have hRpos : 0 < R := by linarith
  -- the derivative of the cutoff vanishes where the cutoff does
  have hsuppD : ∀ z : Plane, 2 * R ≤ |z.2| → deriv (etaCutoff R) z.2 = 0 := by
    intro z hz
    have h := hφd z.2
    rw [hφ0 z.2 hz, Real.sqrt_zero, mul_zero] at h
    exact abs_nonpos_iff.mp h
  -- smoothness of the train at age `s`
  have hSm : TrainSliceSmooth := trainSliceSmooth
  obtain ⟨hv, hp⟩ := hSm ν c tr s hs0
  -- periodicity of the pressure and velocity
  have hpP : ∀ z : Plane, tr.p s (z.1 + c, z.2) = tr.p s z := fun z =>
    tr.isTrain.periodic_p s hs0 z
  have hvP : ∀ z : Plane, tr.v s (z.1 + c, z.2) = tr.v s z := fun z =>
    tr.isTrain.periodic_v s hs0 z
  have hPd : ContDiff ℝ ∞ (tr.p s) := hp
  have hperQ : Cyl.IsPeriodic c (vpIdGq tr R s) := by
    intro z
    show etaCutoff R z.2 * tr.p s (z.1 + c, z.2) * tr.v s (z.1 + c, z.2) 0 =
      etaCutoff R z.2 * tr.p s z * tr.v s z 0
    rw [hpP z, hvP z]
  have hperE : Cyl.IsPeriodic c (vpIdGe tr R s) := by
    intro z
    show etaCutoff R z.2 * tr.p s (z.1 + c, z.2) * tr.v s (z.1 + c, z.2) 1 =
      etaCutoff R z.2 * tr.p s z * tr.v s z 1
    rw [hpP z, hvP z]
  -- the fluxes vanish for `2R ≤ |η|`
  have hsuppQ : ∀ z : Plane, 2 * R ≤ |z.2| → vpIdGq tr R s z = 0 := by
    intro z hz
    simp [vpIdGq, hφ0 z.2 hz]
  have hsuppE : ∀ z : Plane, 2 * R ≤ |z.2| → vpIdGe tr R s z = 0 := by
    intro z hz
    simp [vpIdGe, hφ0 z.2 hz]
  -- smoothness of the fluxes
  have hsnd : ContDiff ℝ ∞ (fun z : Plane => etaCutoff R z.2) := hφS.comp contDiff_snd
  have hGqS : ContDiff ℝ ∞ (vpIdGq tr R s) := (hsnd.mul hPd).mul (prId_comp 0 hv)
  have hGeS : ContDiff ℝ ∞ (vpIdGe tr R s) := (hsnd.mul hPd).mul (prId_comp 1 hv)
  have hGq1 : ContDiff ℝ 1 (vpIdGq tr R s) := hGqS.of_le (by norm_num)
  have hGe1 : ContDiff ℝ 1 (vpIdGe tr R s) := hGeS.of_le (by norm_num)
  -- differentiability
  have hPdiff : Differentiable ℝ (tr.p s) := prId_diff hPd
  have hW0diff : Differentiable ℝ (fun x => tr.v s x 0) := prId_diff (prId_comp 0 hv)
  have hW1diff : Differentiable ℝ (fun x => tr.v s x 1) := prId_diff (prId_comp 1 hv)
  have hφdiff : Differentiable ℝ (etaCutoff R) := hφS.differentiable (by norm_num)
  -- continuity of the basic factors
  have hφC : Continuous (fun z : Plane => etaCutoff R z.2) := hφS.continuous.comp continuous_snd
  have hDφC : Continuous (fun z : Plane => deriv (etaCutoff R) z.2) :=
    (hφS.continuous_deriv (by simp)).comp continuous_snd
  have hPC : Continuous (tr.p s) := hPd.continuous
  have hW1C : Continuous (fun z : Plane => tr.v s z 1) := (prId_comp 1 hv).continuous
  have hWC : Continuous (tr.v s) := hv.continuous
  -- the solenoidal condition
  have hdiv : ∀ z : Plane, Cyl.partialQ (fun x => tr.v s x 0) z +
      Cyl.partialEta (fun x => tr.v s x 1) z = 0 := by
    intro z
    have s1 := tr.isTrain.solenoidal s hs0 z
    unfold Cyl.divergence at s1
    linarith
  -- the pointwise identity `∂_q G_q + ∂_η G_η = φ ⟨v, ∇p⟩ + φ' p v₁`
  have hpt : ∀ z : Plane, Cyl.partialQ (vpIdGq tr R s) z +
      Cyl.partialEta (vpIdGe tr R s) z =
        etaCutoff R z.2 * inner ℝ (tr.v s z) (Train.gradS (tr.p s) z) +
          deriv (etaCutoff R) z.2 * tr.p s z * tr.v s z 1 := by
    intro z
    rw [vpId_Gq_pQ tr R s hPdiff hW0diff z,
      vpId_Ge_pE tr R s hφdiff hPdiff hW1diff z, prId_inner_gradS]
    linear_combination (etaCutoff R z.2 * tr.p s z) * hdiv z
  -- the partial derivatives vanish for `2R ≤ |η|`
  have hQzero : ∀ z : Plane, 2 * R ≤ |z.2| → Cyl.partialQ (vpIdGq tr R s) z = 0 := by
    intro z hz
    rw [vpId_Gq_pQ tr R s hPdiff hW0diff z, hφ0 z.2 hz]
    ring
  have hEzero : ∀ z : Plane, 2 * R ≤ |z.2| → Cyl.partialEta (vpIdGe tr R s) z = 0 := by
    intro z hz
    rw [vpId_Ge_pE tr R s hφdiff hPdiff hW1diff z, hφ0 z.2 hz, hsuppD z hz]
    ring
  -- integrability
  have iQ : IntegrableOn (fun z : Plane => Cyl.partialQ (vpIdGq tr R s) z)
      (Cyl.cell c) :=
    cellToolkit.1 c R hc hRpos _ (prId_pQ_cd hGqS).continuous (fun z hz => hQzero z hz)
  have iE : IntegrableOn (fun z : Plane => Cyl.partialEta (vpIdGe tr R s) z)
      (Cyl.cell c) :=
    cellToolkit.1 c R hc hRpos _ (prId_pE_cd hGeS).continuous (fun z hz => hEzero z hz)
  have iF1 : IntegrableOn (fun z : Plane =>
      etaCutoff R z.2 * inner ℝ (tr.v s z) (Train.gradS (tr.p s) z)) (Cyl.cell c) :=
    cellToolkit.1 c R hc hRpos _ (hφC.mul (hWC.inner (prId_gradS_cont hPd)))
      (fun z hz => by simp [hφ0 z.2 hz])
  have iF2 : IntegrableOn (fun z : Plane =>
      deriv (etaCutoff R) z.2 * tr.p s z * tr.v s z 1) (Cyl.cell c) :=
    cellToolkit.1 c R hc hRpos _ ((hDφC.mul hPC).mul hW1C)
      (fun z hz => by simp [hsuppD z hz])
  -- cell integration by parts
  have hZq := cellToolkit.2 c R hc hRpos (vpIdGq tr R s) hGq1 hperQ hsuppQ
  have hZe := cellToolkit.2 c R hc hRpos (vpIdGe tr R s) hGe1 hperE hsuppE
  have hsplit1 : ∫ z in Cyl.cell c, (etaCutoff R z.2 *
        inner ℝ (tr.v s z) (Train.gradS (tr.p s) z) +
      deriv (etaCutoff R) z.2 * tr.p s z * tr.v s z 1) =
      (∫ z in Cyl.cell c, etaCutoff R z.2 *
        inner ℝ (tr.v s z) (Train.gradS (tr.p s) z)) +
      ∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * tr.p s z * tr.v s z 1 :=
    integral_add iF1 iF2
  have hsplit2 : ∫ z in Cyl.cell c, (Cyl.partialQ (vpIdGq tr R s) z +
        Cyl.partialEta (vpIdGe tr R s) z) =
      (∫ z in Cyl.cell c, Cyl.partialQ (vpIdGq tr R s) z) +
        ∫ z in Cyl.cell c, Cyl.partialEta (vpIdGe tr R s) z :=
    integral_add iQ iE
  have hcongr : ∫ z in Cyl.cell c, (etaCutoff R z.2 *
        inner ℝ (tr.v s z) (Train.gradS (tr.p s) z) +
      deriv (etaCutoff R) z.2 * tr.p s z * tr.v s z 1) =
      ∫ z in Cyl.cell c, (Cyl.partialQ (vpIdGq tr R s) z +
        Cyl.partialEta (vpIdGe tr R s) z) := by
    congr 1
    funext z
    exact (hpt z).symm
  have htot : (∫ z in Cyl.cell c, etaCutoff R z.2 *
        inner ℝ (tr.v s z) (Train.gradS (tr.p s) z)) +
      (∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * tr.p s z * tr.v s z 1) = 0 := by
    rw [← hsplit1, hcongr, hsplit2, hZq.1, hZe.2, add_zero]
  linarith

end UnforcedLeray.Short.PartI

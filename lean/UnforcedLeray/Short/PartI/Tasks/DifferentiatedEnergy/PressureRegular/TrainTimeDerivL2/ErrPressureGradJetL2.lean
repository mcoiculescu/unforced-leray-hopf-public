import UnforcedLeray.Short.PartI.Sub.PartI_T08_3_3
import UnforcedLeray.Short.PartI.Sub.T08_3
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.PressureRegular.PcSmoothDecay
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.PressureRegular.PeriodicDecayBounded
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.PressureRegular.TrainAdvDiffL2
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.PressureRegular.TrainStressDivL2
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.PressureRegular.TrainTimeDerivL2.PressureGradJetL2OfDivForm
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.PressureRegular.TrainTimeDerivL2.ErrPressureLap
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ErrBasic.QcPeriodic
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ForcingIBP

/-!
# Part I, task `PartI:T08/3/3/3` (`ErrPressureGradJetL2`): assembly

Source: `the November 2 reference manuscript` lines 326-336.

For a BUC train and `s > 0` with `width ν s ≤ c²`, the pressure error `π = p - p_c^p` is
smooth, `c`-periodic and bounded (`PcSmoothDecay`, `PeriodicDecayBounded`).  Its Laplacian is
`Δπ = -div F` with `F = advDiff + div Q_c` (`ErrPressureLap`), and `F` is smooth, `c`-periodic
with `L²` word jets (`TrainAdvDiffL2`, `TrainStressDivL2`).  The general lemma
`PressureGradJetL2OfDivForm` (`pressureGradJetL2OfDivForm_proof`) then gives the conclusion.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec Vc pc Qc width)

/-- The advection `(u·∇)u` of a `c`-periodic field is `c`-periodic. -/
theorem errGradAdvPeriodic {c : ℝ} {u : Plane → Vec} (hu : Cyl.IsPeriodic c u) :
    Cyl.IsPeriodic c (Train.advection u) := by
  have h0 : Cyl.IsPeriodic c (fun w => u w 0) := fun w => by
    show u (w.1 + c, w.2) 0 = u w 0
    rw [hu w]
  have h1 : Cyl.IsPeriodic c (fun w => u w 1) := fun w => by
    show u (w.1 + c, w.2) 1 = u w 1
    rw [hu w]
  intro z
  show Train.advection u (z.1 + c, z.2) = Train.advection u z
  unfold Train.advection
  rw [hu z, h0.partialQ z, h0.partialEta z, h1.partialQ z, h1.partialEta z]

/-- The divergence `div Q` of a `c`-periodic tensor field is `c`-periodic. -/
theorem errGradMatDivPeriodic {c : ℝ} {Q : Plane → Matrix (Fin 2) (Fin 2) ℝ}
    (hQ : ∀ k l : Fin 2, Cyl.IsPeriodic c (fun z => Q z k l)) :
    Cyl.IsPeriodic c (Train.matDiv Q) := by
  intro z
  show Train.matDiv Q (z.1 + c, z.2) = Train.matDiv Q z
  unfold Train.matDiv
  rw [(hQ 0 0).partialQ z, (hQ 1 0).partialEta z, (hQ 0 1).partialQ z, (hQ 1 1).partialEta z]

theorem errPressureGradJetL2_proof : UnforcedLeray.Short.PartI.ErrPressureGradJetL2 := by
  intro ν c hν hc tr htr s hs hac
  have hc0 : 0 < c := by linarith
  -- the pressure error: smooth, periodic, bounded
  obtain ⟨hpcs, hpcd⟩ := pcSmoothDecay_proof ν c s hν hc hs.le
  have hps : ContDiff ℝ ∞ (tr.p s) :=
    TrainErrorEquation.contDiff_slice tr.isTrain.smooth_p hs.le
  have hπs : ContDiff ℝ ∞ (errPressure tr s) := hps.sub hpcs
  have hπp : Cyl.IsPeriodic c (errPressure tr s) := by
    intro z
    show tr.p s (z.1 + c, z.2) - pc ν c s (z.1 + c, z.2) = tr.p s z - pc ν c s z
    rw [tr.isTrain.periodic_p s hs.le z, Train.pc_periodic ν c s z]
  have hcont : Continuous (errPressure tr s) := hπs.continuous
  have hdec : Tendsto (errPressure tr s) (comap (fun z : Plane => |z.2|) atTop) (𝓝 0) := by
    have := (tr.isTrain.pressure_decay s hs.le).sub hpcd
    rw [sub_zero] at this
    exact this
  have hbd : ∃ M : ℝ, ∀ z : Plane, |errPressure tr s z| ≤ M :=
    periodicDecayBounded_proof c hc0 _ hcont hπp hdec
  -- the advection bracket and the stress divergence
  obtain ⟨hAc, hAj⟩ := trainAdvDiffL2_proof ν c hν hc tr htr s hs hac
  obtain ⟨hMc, hMj⟩ := trainStressDivL2_proof ν c hν hc tr htr s hs hac
  have comp : ∀ {F : Plane → Vec}, ContDiff ℝ ∞ F → ∀ k : Fin 2,
      ContDiff ℝ ∞ (fun x => F x k) := fun hF k =>
    (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hF
  have hFc : ContDiff ℝ ∞ (fun z => advDiff tr s z + Train.matDiv (Qc ν c s) z) :=
    hAc.add hMc
  have hFj : ∀ (w : List Bool) (k : Fin 2),
      MemLp (wordComp w (fun z => advDiff tr s z + Train.matDiv (Qc ν c s) z) k) 2
        (Cyl.cellμ c) := by
    intro w k
    have e : wordComp w (fun z => advDiff tr s z + Train.matDiv (Qc ν c s) z) k =
        fun z => wordComp w (advDiff tr s) k z + wordComp w (Train.matDiv (Qc ν c s)) k z := by
      unfold wordComp
      exact ForcingIBP.derivWord_add_smooth w (fun x => advDiff tr s x k)
        (fun x => Train.matDiv (Qc ν c s) x k) (comp hAc k) (comp hMc k)
    rw [e]
    exact (hAj w k).add (hMj w k)
  -- periodicity of F
  have hvper : Cyl.IsPeriodic c (tr.v s) := tr.isTrain.periodic_v s hs.le
  have hVper : Cyl.IsPeriodic c (Vc ν c s) := Train.Vc_periodic ν c s
  have hadv : Cyl.IsPeriodic c (advDiff tr s) := by
    intro z
    show Train.advection (tr.v s) (z.1 + c, z.2) - Train.advection (Vc ν c s) (z.1 + c, z.2) =
      Train.advection (tr.v s) z - Train.advection (Vc ν c s) z
    rw [errGradAdvPeriodic hvper z, errGradAdvPeriodic hVper z]
  have hmat : Cyl.IsPeriodic c (Train.matDiv (Qc ν c s)) :=
    errGradMatDivPeriodic (fun k l => qcPeriodic_proof ν c s k l)
  have hFper : Cyl.IsPeriodic c (fun z => advDiff tr s z + Train.matDiv (Qc ν c s) z) := by
    intro z
    show advDiff tr s (z.1 + c, z.2) + Train.matDiv (Qc ν c s) (z.1 + c, z.2) =
      advDiff tr s z + Train.matDiv (Qc ν c s) z
    rw [hadv z, hmat z]
  -- conclude from the general lemma, with the Poisson identity
  exact fun w k =>
    pressureGradJetL2OfDivForm_proof c hc0 (errPressure tr s)
      (fun z => advDiff tr s z + Train.matDiv (Qc ν c s) z) hπs hπp hbd ⟨hFc, hFj⟩ hFper
      (fun z => errPressureLap_proof ν c hν hc tr s hs z) w k

end UnforcedLeray.Short.PartI

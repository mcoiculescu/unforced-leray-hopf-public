import UnforcedLeray.Short.PartI.Sub.T08Statement
import UnforcedLeray.Short.PartI.Sub.PartI_T08_1
import UnforcedLeray.Lib.CylinderB.Periodize
import UnforcedLeray.Short.PartI.Tasks.TrainErrorEquation
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ForcingIBP

/-!
# Part I, task `PartI:T08/3` (`TrainPressureRegular`): decomposition

Source: `the November 2 reference manuscript` lines 266-270 (the train: Gallay-
Slijepcevic existence, BUC and `H^k` data, bounded periodic pressure decaying as `|η| → ∞`) and
326-329 (`p_c^p`, the residual `div Q`).

The pressure error `π = p - p_c^p` is smooth, periodic and decays as `|η| → ∞`, hence bounded.
Its gradient is read off the error equation (`train_error_equation`):
`∇π = νΔe - ∂_s e - A - div Q_c`, `A = v·∇v - V_c·∇V_c`, so every word derivative of `∇π` is
in `L²(cell)` once each of the four terms is smooth with all word derivatives in `L²(cell)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec Vc pc Qc width)

/-- A smooth meridional field with every word derivative of every component in `L²(cell)`. -/
def SmoothJetL2 (c : ℝ) (f : Plane → Vec) : Prop :=
  ContDiff ℝ ∞ f ∧ ∀ (w : List Bool) (k : Fin 2), MemLp (wordComp w f k) 2 (Cyl.cellμ c)

/-- **Leaf (the summed radial pressures)** (lines 326-329: `p_c^p = ∑_n P(· - nc, ·)` with the
isolated radial pressure `P` of the Gaussian vortex, which is smooth with Gaussian decay). For
`ν > 0`, `c ≥ 1`, `s ≥ 0`: `Train.pc ν c s` is `C^∞` and tends to `0` as `|η| → ∞`. -/
def PcSmoothDecay : Prop :=
  ∀ ν c s : ℝ, 0 < ν → 1 ≤ c → 0 ≤ s →
    ContDiff ℝ ∞ (pc ν c s) ∧
      Tendsto (pc ν c s) (comap (fun z : Plane => |z.2|) atTop) (𝓝 0)

/-- **Leaf (real analysis: periodic, continuous, decaying implies bounded).** The cell
`(0, c] × ℝ` is covered by the compact `[0, c] × [-R, R]` and the region `|η| > R`, where
`|f| ≤ 1`; periodicity transports the bound to all of the plane. -/
def PeriodicDecayBounded : Prop :=
  ∀ c : ℝ, 0 < c → ∀ f : Plane → ℝ, Continuous f → Cyl.IsPeriodic c f →
    Tendsto f (comap (fun z : Plane => |z.2|) atTop) (𝓝 0) → ∃ M : ℝ, ∀ z : Plane, |f z| ≤ M

/-- **Leaf (the time derivative of the error)** (lines 261-288: `v` is the finite-energy BUC
mild solution with data in `H^k` for all `k`; `V_c^p` is explicit). At every age `s > 0` with
`a(s) ≤ c²`, `z ↦ ∂_s e(s, z)` is smooth and every word derivative of it is in `L²(cell)`
(`∂_s v = νΔv - v·∇v - ∇p` with `v ∈ H^∞` on `[0, s]`, line 261-288, and `∇p` the Leray
pressure of the nonlinearity; `∂_s V_c^p` is explicit by `Train.Vc_hasDerivAt`). -/
def TrainTimeDerivL2 : Prop :=
  ∀ ν c : ℝ, 0 < ν → 1 ≤ c → ∀ tr : B0140.TrainSol ν c, IsBUCTrain tr → ∀ s : ℝ, 0 < s →
    width ν s ≤ c ^ 2 →
    SmoothJetL2 c (fun z => deriv (fun t => trainErr tr t z) s)

/-- **Leaf (the transport bracket)** (lines 326-329): `A = v·∇v - V_c·∇V_c =
(V_c·∇)e + (e·∇)V_c + (e·∇)e` is smooth with every word derivative in `L²(cell)`: Leibniz on the
words, with `|∂_w V_c| ≤ C a^{-(3+|w|)/2}` (`Vc_word_bound`), bounded word derivatives of `e`
(`trainErrBasic_proof`) and `L²` word derivatives of `e` (`trainErrJetL2_proof`). -/
def TrainAdvDiffL2 : Prop :=
  ∀ ν c : ℝ, 0 < ν → 1 ≤ c → ∀ tr : B0140.TrainSol ν c, IsBUCTrain tr → ∀ s : ℝ, 0 < s →
    width ν s ≤ c ^ 2 → SmoothJetL2 c (advDiff tr s)

/-- **Leaf (the viscous term)**: `νΔe` is smooth with all word derivatives in `L²(cell)`; a word
derivative of `Δe` is a word derivative of `e` of two higher order (`trainErrJetL2_proof`). -/
def TrainErrLaplacianL2 : Prop :=
  ∀ ν c : ℝ, 0 < ν → 1 ≤ c → ∀ tr : B0140.TrainSol ν c, IsBUCTrain tr → ∀ s : ℝ, 0 < s →
    width ν s ≤ c ^ 2 → SmoothJetL2 c (ν • Train.vecLaplacian (trainErr tr s))

/-- **Leaf (the stress divergence)** (lines 326-329): `div Q_c(s)` is smooth with all word
derivatives in `L²(cell)`: its components are `∂_k Q^{kl}`, word derivatives of the entries of
`Q_c` (`vcStressJetBound_proof`, first conjunct, and `QcSmooth`). -/
def TrainStressDivL2 : Prop :=
  ∀ ν c : ℝ, 0 < ν → 1 ≤ c → ∀ tr : B0140.TrainSol ν c, IsBUCTrain tr → ∀ s : ℝ, 0 < s →
    width ν s ≤ c ^ 2 → SmoothJetL2 c (Train.matDiv (Qc ν c s))

theorem wordL2_sub {c : ℝ} {f g : Plane → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (h1 : ∀ w : List Bool, MemLp (B0151.derivWord w f) 2 (Cyl.cellμ c))
    (h2 : ∀ w : List Bool, MemLp (B0151.derivWord w g) 2 (Cyl.cellμ c)) (w : List Bool) :
    MemLp (B0151.derivWord w (fun x => f x - g x)) 2 (Cyl.cellμ c) := by
  have e : B0151.derivWord w (fun x => f x - g x) =
      fun z => B0151.derivWord w f z - B0151.derivWord w g z :=
    funext (derivWord_sub_smooth hf hg w)
  rw [e]
  exact (h1 w).sub (h2 w)

theorem trainPressureRegular_of (h1 : PcSmoothDecay) (h2 : PeriodicDecayBounded)
    (h3 : TrainTimeDerivL2) (h4 : TrainAdvDiffL2) (h5 : TrainErrLaplacianL2)
    (h6 : TrainStressDivL2) : TrainPressureRegular := by
  intro ν c hν hc tr htr s hs hac
  have hc0 : 0 < c := by linarith
  obtain ⟨hpcs, hpcd⟩ := h1 ν c s hν hc hs.le
  have hps : ContDiff ℝ ∞ (tr.p s) :=
    TrainErrorEquation.contDiff_slice tr.isTrain.smooth_p hs.le
  have hπs : ContDiff ℝ ∞ (errPressure tr s) := hps.sub hpcs
  have hπp : Cyl.IsPeriodic c (errPressure tr s) := by
    intro z
    show tr.p s (z.1 + c, z.2) - pc ν c s (z.1 + c, z.2) = tr.p s z - pc ν c s z
    have hpp : pc ν c s (z.1 + c, z.2) = pc ν c s z :=
      Cyl.isPeriodic_periodize c (Train.isoP ν s) z
    rw [tr.isTrain.periodic_p s hs.le z, hpp]
  have hcont : Continuous (errPressure tr s) := hπs.continuous
  have hdec : Tendsto (errPressure tr s) (comap (fun z : Plane => |z.2|) atTop) (𝓝 0) := by
    have := (tr.isTrain.pressure_decay s hs.le).sub hpcd
    rw [sub_zero] at this
    exact this
  refine ⟨hπs, hπp, h2 c hc0 _ hcont hπp hdec, ?_⟩
  -- the gradient from the error equation
  have hX := h5 ν c hν hc tr htr s hs hac
  have hY := h3 ν c hν hc tr htr s hs hac
  have hA := h4 ν c hν hc tr htr s hs hac
  have hM := h6 ν c hν hc tr htr s hs hac
  have comp : ∀ {F : Plane → Vec}, ContDiff ℝ ∞ F → ∀ k : Fin 2,
      ContDiff ℝ ∞ (fun x => F x k) := fun hF k =>
    (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hF
  intro w k
  have key : (fun z => Train.gradS (errPressure tr s) z k) = fun z =>
      (((ν • Train.vecLaplacian (trainErr tr s)) z k -
        (fun z => deriv (fun t => trainErr tr t z) s) z k) - advDiff tr s z k) -
        Train.matDiv (Qc ν c s) z k := by
    funext z
    have h := TrainErrorEquation.train_error_equation tr hν hc0.ne' s hs z
    have h' := congrArg (fun x : Vec => x k) h
    simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.neg_apply, PiLp.smul_apply] at h'
    show (Train.gradS (fun w => tr.p s w - pc ν c s w) z).ofLp k = _
    simp only [PiLp.smul_apply, PiLp.sub_apply, advDiff, Pi.smul_apply]
    change _ = ν • (Train.vecLaplacian (fun w => tr.v s w - Vc ν c s w) z).ofLp k -
        (deriv (fun t => tr.v t z - Vc ν c t z) s).ofLp k -
        ((Train.advection (tr.v s) z).ofLp k - (Train.advection (Vc ν c s) z).ofLp k) -
        (Train.matDiv (Qc ν c s) z).ofLp k
    linarith
  have e : wordComp w (Train.gradS (errPressure tr s)) k =
      B0151.derivWord w (fun z => (((ν • Train.vecLaplacian (trainErr tr s)) z k -
        (fun z => deriv (fun t => trainErr tr t z) s) z k) - advDiff tr s z k) -
        Train.matDiv (Qc ν c s) z k) := by
    unfold wordComp
    rw [key]
  rw [e]
  have cX := comp hX.1
  have cY := comp hY.1
  have cA := comp hA.1
  have cM := comp hM.1
  have l1 : ∀ w : List Bool, MemLp (B0151.derivWord w (fun z =>
      ((ν • Train.vecLaplacian (trainErr tr s)) z k -
        (fun z => deriv (fun t => trainErr tr t z) s) z k) - advDiff tr s z k)) 2 (Cyl.cellμ c) :=
    fun w => wordL2_sub ((cX k).sub (cY k)) (cA k)
      (fun w => wordL2_sub (cX k) (cY k) (fun w => hX.2 w k) (fun w => hY.2 w k) w)
      (fun w => hA.2 w k) w
  exact wordL2_sub (((cX k).sub (cY k)).sub (cA k)) (cM k) l1 (fun w => hM.2 w k) w

end UnforcedLeray.Short.PartI

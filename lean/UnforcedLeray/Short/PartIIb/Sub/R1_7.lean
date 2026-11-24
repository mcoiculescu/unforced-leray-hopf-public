import UnforcedLeray.Short.PartIIb.Sub.R1
import UnforcedLeray.Short.PartI.Sub.T01
import UnforcedLeray.Lib.Axisymmetric.Laplacian
import UnforcedLeray.Units.B0140
import UnforcedLeray.Units.B0185
import UnforcedLeray.Units.B0187
import UnforcedLeray.Units.B0190

/-!
# Part II-b, task `PartII-b:R1/7`: the ring residual is the Cartesian Navier-Stokes residual
(conditional)

Source of record: `the November 2 reference manuscript`, lines 1203-1263
(Proposition `sct:lift`: the physical lift `u_r = (R/r) v_1`, `u_z = (R/r)(v_2 + εH)`,
`p_raw = (R/r)^2 p`; the residual is `F_R = s^{3/2} r`, line 1263) and lines 2042-2046
(`F_R` is the similarity residual of `U_raw`); `paper/main.tex` 2867-2888 (B0187, cylindrical
residual of an axisymmetric no-swirl field).

Target (`Sub/R1.lean`): `RingResidualCartesianNS`: for `ν, c > 0`, `R ≥ 2`, an exact planar
(BUC) train `(ψ, pr)` and `C^∞` fields `U, Pw` on `ℝ × ℝ³` agreeing off the axis with the
similarity lift,
`realC (ringResidual R ν ψ pr τ y) = L₀U + (U·∇)U + ∇Pw` at every off-axis `(τ, y)`.

## Proof (assembled below from named leaf Props)

1. *Locality* (`operatorLocality`, PROVED here): `L₀ + advT + gradT` at a point depend only on the
   germ of `(U, Pw)`, so `(U, Pw)` may be replaced by the explicit lifts `W, Q` (they agree on the
   open set `{ϱ y ≠ 0}`).
2. *Scaling* (`SimT0Scaling`, `SimLapScaling`, `SimAdvScaling`, `SimGradScaling`): for any physical field `u(t, x)`,
   `π(t, x)` that is `C²` near `(e^τ, e^{τ/2} y)`, with `W = e^{τ/2} u(e^τ, e^{τ/2} y)`,
   `Q = e^τ π(e^τ, e^{τ/2} y)`:
   `L₀W = T₀W - νΔW - W/2 = e^{3τ/2}(u_t - νΔu)`, `(W·∇)W = e^{3τ/2}(u·∇)u`, `∇Q = e^{3τ/2}∇π`.
3. *Cartesian = cylindrical* (`CylTimeFormula`, `CylAdvFormula`, `CylLapFormula`,
   `CylGradFormula`): for the meridional lift `u = u_r e_r + u_z e_z`, `π`, off the axis,
   `u_t`, `(u·∇)u`, `Δu` (vector Laplacian), `∇π` are the `e_r`, `e_z` components in the
   cylindrical residual of B0187; summed they are `physResidualField`.
4. *Smoothness* (`LiftMeridSmooth`, `CylFieldSmooth`, `TrainPressureSmooth`,
   `TrainStreamSmoothBUC`): the lift of the train is `C²` jointly in `(r, z, t)` on `{r, t > 0}`
   (the BUC train is smooth at positive age, SP 261-288), hence the Cartesian lift is `C²` near
   off-axis points of positive time.

Proved here: `operatorLocality`, `trainStreamSmoothBUC_of` (from `PartI.TrainStreamSmooth`) and
`ringResidualCartesianNS_of` (zero sorry; axioms `propext, Classical.choice, Quot.sound`; audit
file `Sub/R1_7/Audit.lean`). The leaf Props are proved by tasks `PartII-b:R1/7/1 ... R1/7/11`,
files `Short/PartII-b/Tasks/RawResidualFamily/RingCartesianNS/*.lean`; `PartI.TrainStreamSmooth`
is the task `PartI:T01/1` (`theorem trainStreamSmooth`,
`Short/PartI/Tasks/TrainMeanEquations/StreamSmooth.lean`).

## Status without inflation

* The stream smoothness is used only for the BUC train (`IsExactPlanarTrain` carries
  `PartI.IsBUCTrain T`) and only for `ν, c > 0` (`RingResidualCartesianNS` assumes `0 < ν`,
  `0 < c`; its consumer `rawResidualWeakIdentity_of` supplies `p.ν_pos`, `p.c_pos`). In this form
  it is `PartI.TrainStreamSmooth` composed with the chart swap (`trainStreamSmoothBUC_of`), so the
  unconditional target depends on `PartI:T01/1`.
* `TrainPressureSmooth` IS a consequence of `IsTrain.smooth_p` (leaf task).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412 UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0187
  UnforcedLeray.Short.PartIIa

/-! ## Objects -/

/-- The Cartesian field of a meridional pair: `u(t, x) = u_r(ϱ x, x₃, t) e_r(x) + u_z(ϱ x, x₃, t) e₃`
(`B0185.liftVelocity_apply` shows `liftVelocity R ψ t = cylField (liftUr R ψ) (liftUz R ψ) t`). -/
def cylField (ur uz : ℝ → ℝ → ℝ → ℝ) (t : ℝ) (x : Space) : Space :=
  ur (Axi.ϱ x) (x 2) t • Axi.eR x + uz (Axi.ϱ x) (x 2) t • Axi.e3

/-- The Cartesian scalar of a meridional scalar: `π(t, x) = p(ϱ x, x₃, t)`
(`B0185.liftPressure R p t = cylPressure (rawPressure R p) t`, by `rfl`). -/
def cylPressure (p : ℝ → ℝ → ℝ → ℝ) (t : ℝ) (x : Space) : ℝ := p (Axi.ϱ x) (x 2) t

/-- The Cartesian gradient `(∂₁f, ∂₂f, ∂₃f)` of a scalar function on `ℝ³`. -/
def cartGrad (f : Space → ℝ) (x : Space) : Space :=
  !₂[fderiv ℝ f x (coordinateVector 0), fderiv ℝ f x (coordinateVector 1),
    fderiv ℝ f x (coordinateVector 2)]

/-- The open domain `{(r, z, t) : r > 0, t > 0}` in meridional-time coordinates. -/
def meridDomain : Set (ℝ × ℝ × ℝ) := {q | 0 < q.1 ∧ 0 < q.2.2}

/-- `f(r, z, t)` is `C^n` jointly in `(r, z, t)` on `{r > 0, t > 0}`. -/
def MeridSmooth (n : WithTop ℕ∞) (f : ℝ → ℝ → ℝ → ℝ) : Prop :=
  ContDiffOn ℝ n (fun q : ℝ × ℝ × ℝ => f q.1 q.2.1 q.2.2) meridDomain

theorem MeridSmooth.of_le {m n : WithTop ℕ∞} (h : m ≤ n) {f : ℝ → ℝ → ℝ → ℝ}
    (hf : MeridSmooth n f) : MeridSmooth m f :=
  ContDiffOn.of_le hf h

/-! ## Step 1: locality of the operators (proved) -/

/-- **Locality.** `L₀ + advT + gradT` at `z` depend only on the germ at `z` of the fields. -/
theorem operatorLocality (ν : ℝ) (U W : ℝ × Space → CVec3) (P Q : ℝ × Space → ℂ)
    (z : ℝ × Space) (hUW : U =ᶠ[𝓝 z] W) (hPQ : P =ᶠ[𝓝 z] Q) :
    L0 ν U z + advT U U z + gradT P z = L0 ν W z + advT W W z + gradT Q z := by
  have key : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (f g : ℝ × Space → E)
      (w : ℝ × Space), f =ᶠ[𝓝 w] g → (∀ j : Fin 3, dy j f w = dy j g w) ∧ dτ f w = dτ g w := by
    intro E _ _ f g w h
    exact ⟨fun j => by unfold dy; rw [h.fderiv_eq], by unfold dτ; rw [h.fderiv_eq]⟩
  have e1 : dτ U z = dτ W z := (key U W z hUW).2
  have e2 : ∀ j : Fin 3, dy j U z = dy j W z := (key U W z hUW).1
  have e3 : ∀ j : Fin 3, dy j (dy j U) z = dy j (dy j W) z := by
    intro j
    have hev : dy j U =ᶠ[𝓝 z] dy j W :=
      hUW.eventuallyEq_nhds.mono fun w hw => (key U W w hw).1 j
    exact (key _ _ z hev).1 j
  have e4 : U z = W z := hUW.eq_of_nhds
  have e5 : ∀ j : Fin 3, dy j P z = dy j Q z := (key P Q z hPQ).1
  simp only [L0, T0, lapT, radialT, advT, gradT, e1, e2, e3, e4, e5]

/-! ## Step 2: similarity scaling (leaf Props) -/

/-- **Scaling of the drift `T₀ = ∂_τ - ½ y·∇`** (SP 1263; `B0411.T0`, `B0190.simProfile`): for a
physical field `u(t, x)` differentiable (jointly) at `(e^τ, e^{τ/2} y)`, the similarity field
`W(τ, y) = realC (e^{τ/2} u(e^τ, e^{τ/2} y))` satisfies, with `t = e^τ`, `x = e^{τ/2} y`,
`T₀ W (τ, y) = realC (½ e^{τ/2} u(t, x) + e^{3τ/2} ∂_t u(t, x))`.
(`∂_τ W = W/2 + e^{τ/2}(t u_t + ½ x·∇u)` and `y·∇_y W = e^{τ/2} x·∇u`; `x·∇u = D(u t)(x)(x)`.) -/
def SimT0Scaling : Prop :=
  ∀ (u : ℝ → Space → Space) (τ : ℝ) (y : Space),
    DifferentiableAt ℝ (fun q : ℝ × Space => u q.1 q.2) (Real.exp τ, Real.exp (τ / 2) • y) →
    T0 (fun q : ℝ × Space => realC (UnforcedLeray.B0190.simProfile 1 u q.1 q.2)) (τ, y) =
      realC ((1 / 2 : ℝ) • (Real.exp (τ / 2) • u (Real.exp τ) (Real.exp (τ / 2) • y)) +
        Real.exp (τ / 2) ^ 3 • deriv (fun s => u s (Real.exp (τ / 2) • y)) (Real.exp τ))

/-- **Scaling of the Laplacian** (`Lib/PhaseSpace/Ops.lean` `lapT`): for a physical field `u(t, x)`,
`C²` jointly near `(e^τ, e^{τ/2} y)`, `Δ_y W (τ, y) = realC (e^{3τ/2} Δu (e^τ, e^{τ/2} y))`
with `Δ = Axi.vecLap` (`∂_{y_j} W = e^τ ∂_j u`, `∂_{y_j}² W = e^{3τ/2} ∂_j² u`). -/
def SimLapScaling : Prop :=
  ∀ (u : ℝ → Space → Space) (τ : ℝ) (y : Space),
    ContDiffAt ℝ 2 (fun q : ℝ × Space => u q.1 q.2) (Real.exp τ, Real.exp (τ / 2) • y) →
    lapT (fun q : ℝ × Space => realC (UnforcedLeray.B0190.simProfile 1 u q.1 q.2)) (τ, y) =
      realC (Real.exp (τ / 2) ^ 3 • Axi.vecLap (u (Real.exp τ)) (Real.exp (τ / 2) • y))

/-- **Scaling of the advection** (`Cons/L2/BackgroundConcrete/Operators.lean` `advT`): for `u` differentiable
(jointly) at `(e^τ, e^{τ/2} y)`, `advT W W (τ, y) = realC (e^{3τ/2} (u·∇)u (e^τ, e^{τ/2} y))`,
`(u·∇)u = Axi.advection (u t) (u t) x = D(u t)(x)(u t x)`. -/
def SimAdvScaling : Prop :=
  ∀ (u : ℝ → Space → Space) (τ : ℝ) (y : Space),
    DifferentiableAt ℝ (fun q : ℝ × Space => u q.1 q.2) (Real.exp τ, Real.exp (τ / 2) • y) →
    advT (fun q : ℝ × Space => realC (UnforcedLeray.B0190.simProfile 1 u q.1 q.2))
        (fun q : ℝ × Space => realC (UnforcedLeray.B0190.simProfile 1 u q.1 q.2)) (τ, y) =
      realC (Real.exp (τ / 2) ^ 3 •
        Axi.advection (u (Real.exp τ)) (u (Real.exp τ)) (Real.exp (τ / 2) • y))

/-- **Scaling of the pressure gradient** (`Lib/PhaseSpace/Ops.lean` `gradT`): for `π` differentiable
(jointly) at `(e^τ, e^{τ/2} y)`, with `Q(τ, y) = ((e^τ π(e^τ, e^{τ/2} y) : ℝ) : ℂ)`,
`gradT Q (τ, y) = realC (e^{3τ/2} ∇π (e^τ, e^{τ/2} y))`. -/
def SimGradScaling : Prop :=
  ∀ (π : ℝ → Space → ℝ) (τ : ℝ) (y : Space),
    DifferentiableAt ℝ (fun q : ℝ × Space => π q.1 q.2) (Real.exp τ, Real.exp (τ / 2) • y) →
    gradT (fun q : ℝ × Space => ((UnforcedLeray.B0190.simProfile 2 π q.1 q.2 : ℝ) : ℂ)) (τ, y) =
      realC (Real.exp (τ / 2) ^ 3 • cartGrad (π (Real.exp τ)) (Real.exp (τ / 2) • y))

/-! ## Step 3: Cartesian = cylindrical for meridional fields (leaf Props) -/

/-- **Time derivative of the meridional lift**: off the axis, at `t > 0`,
`∂_t (u_r e_r + u_z e_z) = (∂_t u_r) e_r + (∂_t u_z) e_z` (`B0187.physT`), for `u_r, u_z` of class
`C¹` jointly on `{r, t > 0}`. -/
def CylTimeFormula : Prop :=
  ∀ (ur uz : ℝ → ℝ → ℝ → ℝ) (t : ℝ) (x : Space), 0 < t → x ∉ Axi.axis →
    MeridSmooth 1 ur → MeridSmooth 1 uz →
    deriv (fun s => cylField ur uz s x) t =
      physT ur (Axi.ϱ x) (x 2) t • Axi.eR x + physT uz (Axi.ϱ x) (x 2) t • Axi.e3

/-- **Advection of the meridional lift** (`Axi.advection_liftMer`): off the axis,
`(u·∇)u = (u_r ∂_r u_r + u_z ∂_z u_r) e_r + (u_r ∂_r u_z + u_z ∂_z u_z) e_z`
(`B0187.physR`, `physZ`), no hoop term (no swirl). -/
def CylAdvFormula : Prop :=
  ∀ (ur uz : ℝ → ℝ → ℝ → ℝ) (t : ℝ) (x : Space), 0 < t → x ∉ Axi.axis →
    MeridSmooth 1 ur → MeridSmooth 1 uz →
    Axi.advection (cylField ur uz t) (cylField ur uz t) x =
      (ur (Axi.ϱ x) (x 2) t * physR ur (Axi.ϱ x) (x 2) t
          + uz (Axi.ϱ x) (x 2) t * physZ ur (Axi.ϱ x) (x 2) t) • Axi.eR x +
      (ur (Axi.ϱ x) (x 2) t * physR uz (Axi.ϱ x) (x 2) t
          + uz (Axi.ϱ x) (x 2) t * physZ uz (Axi.ϱ x) (x 2) t) • Axi.e3

/-- **Vector Laplacian of the meridional lift** (`Axi.vecLap_liftMer`): off the axis,
`Δ(u_r e_r + u_z e_z) = (∂_r² + r⁻¹∂_r - r⁻² + ∂_z²)u_r e_r + (∂_r² + r⁻¹∂_r + ∂_z²)u_z e_z`
(`B0187.radialVectorLaplacian`, `axialVectorLaplacian`), for `C²` profiles. -/
def CylLapFormula : Prop :=
  ∀ (ur uz : ℝ → ℝ → ℝ → ℝ) (t : ℝ) (x : Space), 0 < t → x ∉ Axi.axis →
    MeridSmooth 2 ur → MeridSmooth 2 uz →
    Axi.vecLap (cylField ur uz t) x =
      radialVectorLaplacian ur (Axi.ϱ x) (x 2) t • Axi.eR x +
        axialVectorLaplacian uz (Axi.ϱ x) (x 2) t • Axi.e3

/-- **Gradient of the meridional scalar**: off the axis, `∇ p(ϱ x, x₃, t) = ∂_r p e_r + ∂_z p e_z`
(`Axi.fderiv_comp_mer_apply`), for `p` of class `C¹`. -/
def CylGradFormula : Prop :=
  ∀ (p : ℝ → ℝ → ℝ → ℝ) (t : ℝ) (x : Space), 0 < t → x ∉ Axi.axis → MeridSmooth 1 p →
    cartGrad (cylPressure p t) x =
      physR p (Axi.ϱ x) (x 2) t • Axi.eR x + physZ p (Axi.ϱ x) (x 2) t • Axi.e3

/-! ## Step 4: smoothness (leaf Props) -/

/-- **The lifted profiles are `C²` jointly in `(r, z, t)` on `{r, t > 0}`**
(`B0185.liftUr = scaledLift R 1 (streamV1 ψ)`, `liftUz = scaledLift R 1 (axialProfile R ψ)`,
`rawPressure = scaledLift R 2 pr`; the chart `(r, z, t) ↦ (R log(r/R), Rz/r, R²t/r²)` is smooth on
`r > 0` and maps `{r, t > 0}` into the open age domain `{s > 0}`; `streamV1`, `axialProfile` are
first-order expressions in `ψ`, so `ψ ∈ C³` on the age domain gives `C²`). -/
def LiftMeridSmooth : Prop :=
  ∀ (R : ℝ) (ψ pr : ProfilePoint → ℝ), 2 ≤ R →
    ContDiffOn ℝ 3 ψ ageDomain → ContDiffOn ℝ 2 pr ageDomain →
    MeridSmooth 2 (liftUr R ψ) ∧ MeridSmooth 2 (liftUz R ψ) ∧ MeridSmooth 2 (rawPressure R pr)

/-- **The Cartesian field of `C²` meridional profiles is `C²` jointly in `(t, x)`** off the axis
at positive time (`Axi.contDiffOn_liftMer`-style: `ϱ`, `eR` are smooth off the axis). -/
def CylFieldSmooth : Prop :=
  ∀ (ur uz p : ℝ → ℝ → ℝ → ℝ) (t : ℝ) (x : Space), 0 < t → x ∉ Axi.axis →
    MeridSmooth 2 ur → MeridSmooth 2 uz → MeridSmooth 2 p →
    ContDiffAt ℝ 2 (fun q : ℝ × Space => cylField ur uz q.1 q.2) (t, x) ∧
    ContDiffAt ℝ 2 (fun q : ℝ × Space => cylPressure p q.1 q.2) (t, x)

/-- **The pressure profile of a train is smooth at positive age** (SP 261-288: the train is a
global smooth solution; `IsTrain.smooth_p` is smoothness on `[0, ∞) × ℝ²`; compose with the
coordinate change `(q, η, s) ↦ (s, (q, η))`). A consequence of the fields of `B0140.IsTrain`. -/
def TrainPressureSmooth : Prop :=
  ∀ (ν c : ℝ) (T : UnforcedLeray.B0140.TrainSol ν c),
    ContDiffOn ℝ ∞ (UnforcedLeray.B0190.trainProfile T.p) ageDomain

/-- **The stream profile of the BUC train is smooth at positive age** (SP 261-288: the
Gallay-Slijepčević solution in `BUC` is smooth for positive time; SP 1203-1250: the lift is smooth
for positive time). For `ν, c > 0` and a train `T` of the BUC class, `ψ(q, η, s)` is `C^∞` on the
age domain `{s > 0}`. The profile form of `PartI.TrainStreamSmooth` (`trainStreamSmoothBUC_of`). -/
def TrainStreamSmoothBUC : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ T : UnforcedLeray.B0140.TrainSol ν c,
    UnforcedLeray.Short.PartI.IsBUCTrain T →
    ContDiffOn ℝ ∞ (UnforcedLeray.B0190.trainProfile T.ψ) ageDomain

/-- **`TrainStreamSmoothBUC` from `PartI.TrainStreamSmooth`**: compose the smoothness of
`(s, (q, η)) ↦ ψ(s, (q, η))` on `Ioi 0 ×ˢ univ` with the linear chart swap
`(q, (η, s)) ↦ (s, (q, η))`, which maps `ageDomain` into `Ioi 0 ×ˢ univ`
(as `PartIIa.lateProfileSmooth_of`, `Short/PartII-a/Tasks/R02/ProfileSmooth.lean`). -/
theorem trainStreamSmoothBUC_of (h : UnforcedLeray.Short.PartI.TrainStreamSmooth) :
    TrainStreamSmoothBUC := by
  intro ν c hν hc T hT
  have hψ := h ν c hν hc T hT
  have hL : ContDiff ℝ ∞ (fun x : ProfilePoint => (x.2.2, (x.1, x.2.1))) := by fun_prop
  have hM : MapsTo (fun x : ProfilePoint => (x.2.2, (x.1, x.2.1))) ageDomain
      (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := fun x hx =>
    Set.mk_mem_prod (show (0 : ℝ) < x.2.2 from hx) (Set.mem_univ _)
  exact ContDiffOn.comp hψ hL.contDiffOn hM

/-! ## The conditional theorem -/

theorem realC_add_aux (a b : Space) : realC (a + b) = realC a + realC b := by
  ext i
  simp [realC_apply]

theorem realC_sub_aux (a b : Space) : realC (a - b) = realC a - realC b := by
  ext i
  simp [realC_apply]

theorem realC_smul_aux (c : ℝ) (a : Space) : realC (c • a) = c • realC a := by
  ext i
  simp [realC_apply]

/-- **`RingResidualCartesianNS`, conditional on the leaf Props.** -/
theorem ringResidualCartesianNS_of
    (h0 : SimT0Scaling) (hLp : SimLapScaling) (hA : SimAdvScaling) (hG : SimGradScaling)
    (hT : CylTimeFormula) (hAd : CylAdvFormula) (hL : CylLapFormula) (hGr : CylGradFormula)
    (hLift : LiftMeridSmooth) (hCyl : CylFieldSmooth)
    (hP : TrainPressureSmooth) (hS : TrainStreamSmoothBUC) : RingResidualCartesianNS := by
  intro ν c R ψ pr hν hc hR hTr U Pw hU hPw hagree τ y hy
  obtain ⟨T, hBUC, rfl, rfl⟩ := hTr
  set t : ℝ := Real.exp τ with ht_def
  set x : Space := Real.exp (τ / 2) • y with hx_def
  have ht : 0 < t := Real.exp_pos τ
  have hx : x ∉ Axi.axis := by
    rw [Axi.mem_axis_iff, hx_def, Axi.ϱ_smul, abs_of_pos (Real.exp_pos _)]
    exact mul_ne_zero (Real.exp_pos _).ne' hy
  -- smoothness of the profiles at positive age
  have hψ3 : ContDiffOn ℝ 3 (UnforcedLeray.B0190.trainProfile T.ψ) ageDomain :=
    (hS ν c hν hc T hBUC).of_le (by simp)
  have hp2 : ContDiffOn ℝ 2 (UnforcedLeray.B0190.trainProfile T.p) ageDomain :=
    (hP ν c T).of_le (by simp)
  obtain ⟨m1, m2, m3⟩ := hLift R (UnforcedLeray.B0190.trainProfile T.ψ)
    (UnforcedLeray.B0190.trainProfile T.p) hR hψ3 hp2
  obtain ⟨hu0, hπ0⟩ := hCyl _ _ _ t x ht hx m1 m2 m3
  have hveq : liftVelocity R (UnforcedLeray.B0190.trainProfile T.ψ) =
      cylField (liftUr R (UnforcedLeray.B0190.trainProfile T.ψ))
        (liftUz R (UnforcedLeray.B0190.trainProfile T.ψ)) := by
    funext s w
    exact liftVelocity_apply R _ s w
  have hpeq : liftPressure R (UnforcedLeray.B0190.trainProfile T.p) =
      cylPressure (rawPressure R (UnforcedLeray.B0190.trainProfile T.p)) := by
    funext s w
    rfl
  have hu : ContDiffAt ℝ 2 (fun q : ℝ × Space =>
      liftVelocity R (UnforcedLeray.B0190.trainProfile T.ψ) q.1 q.2) (t, x) := by
    rw [hveq]; exact hu0
  have hπ : ContDiffAt ℝ 2 (fun q : ℝ × Space =>
      liftPressure R (UnforcedLeray.B0190.trainProfile T.p) q.1 q.2) (t, x) := by
    rw [hpeq]; exact hπ0
  -- scaling
  have s0a := h0 (liftVelocity R (UnforcedLeray.B0190.trainProfile T.ψ)) τ y
    (hu.differentiableAt (by norm_num))
  have s0b := hLp (liftVelocity R (UnforcedLeray.B0190.trainProfile T.ψ)) τ y hu
  have s0 : L0 ν (fun q : ℝ × Space => realC (UnforcedLeray.B0190.simProfile 1
        (liftVelocity R (UnforcedLeray.B0190.trainProfile T.ψ)) q.1 q.2)) (τ, y) =
      realC (Real.exp (τ / 2) ^ 3 •
        (deriv (fun s => liftVelocity R (UnforcedLeray.B0190.trainProfile T.ψ) s x) t
          - ν • Axi.vecLap (liftVelocity R (UnforcedLeray.B0190.trainProfile T.ψ) t) x)) := by
    simp only [L0]
    rw [s0a, s0b]
    simp only [UnforcedLeray.B0190.simProfile, pow_one]
    rw [← realC_smul_aux, ← realC_smul_aux, ← realC_sub_aux, ← realC_sub_aux]
    congr 1
    module
  have s1 := hA (liftVelocity R (UnforcedLeray.B0190.trainProfile T.ψ)) τ y
    (hu.differentiableAt (by norm_num))
  have s2 := hG (liftPressure R (UnforcedLeray.B0190.trainProfile T.p)) τ y
    (hπ.differentiableAt (by norm_num))
  -- cylindrical formulas
  have c0 := hT _ _ t x ht hx (m1.of_le (by norm_num)) (m2.of_le (by norm_num))
  have c1 := hAd _ _ t x ht hx (m1.of_le (by norm_num)) (m2.of_le (by norm_num))
  have c2 := hL _ _ t x ht hx m1 m2
  have c3 := hGr _ t x ht hx (m3.of_le (by norm_num))
  rw [← hveq] at c0 c1 c2
  rw [← hpeq] at c3
  -- the residual as a Space identity
  have hres : ringResidual R ν (UnforcedLeray.B0190.trainProfile T.ψ)
        (UnforcedLeray.B0190.trainProfile T.p) τ y =
      Real.exp (τ / 2) ^ 3 •
        (deriv (fun s => liftVelocity R (UnforcedLeray.B0190.trainProfile T.ψ) s x) t
          - ν • Axi.vecLap (liftVelocity R (UnforcedLeray.B0190.trainProfile T.ψ) t) x) +
      Real.exp (τ / 2) ^ 3 •
        Axi.advection (liftVelocity R (UnforcedLeray.B0190.trainProfile T.ψ) t)
          (liftVelocity R (UnforcedLeray.B0190.trainProfile T.ψ) t) x +
      Real.exp (τ / 2) ^ 3 •
        cartGrad (liftPressure R (UnforcedLeray.B0190.trainProfile T.p) t) x := by
    rw [c0, c1, c2, c3]
    simp only [ringResidual, physResidualField, cylRadialResidual, cylAxialResidual]
    module
  -- agreement near the point
  have hopen : IsOpen {q : ℝ × Space | Axi.ϱ q.2 ≠ 0} :=
    isOpen_ne_fun (Axi.continuous_ϱ.comp continuous_snd) continuous_const
  have hUW : U =ᶠ[𝓝 (τ, y)] (fun q : ℝ × Space =>
      realC (UnforcedLeray.B0190.simProfile 1
        (liftVelocity R (UnforcedLeray.B0190.trainProfile T.ψ)) q.1 q.2)) :=
    Filter.eventuallyEq_of_mem (hopen.mem_nhds (show Axi.ϱ (τ, y).2 ≠ 0 from hy))
      (fun q hq => (hagree q hq).1)
  have hPQ : Pw =ᶠ[𝓝 (τ, y)] (fun q : ℝ × Space =>
      ((UnforcedLeray.B0190.simProfile 2
        (liftPressure R (UnforcedLeray.B0190.trainProfile T.p)) q.1 q.2 : ℝ) : ℂ)) :=
    Filter.eventuallyEq_of_mem (hopen.mem_nhds (show Axi.ϱ (τ, y).2 ≠ 0 from hy))
      (fun q hq => (hagree q hq).2)
  rw [operatorLocality ν U _ Pw _ (τ, y) hUW hPQ, s0, s1, s2, hres, realC_add_aux,
    realC_add_aux]

end UnforcedLeray.Short.IIb

end

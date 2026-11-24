import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.OuterGen.Transp.Deriv.Defs
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.OuterGen.Transp.Deriv.OdExists
import UnforcedLeray.Short.PartIIa.Tasks.F05aAdjResolventSolution.HeatGaussEquation

/-!
# `odHeatTaylor` decomposed (task `PartIII-b:C/near/pins/3/4/2/3/2/4/13`)

Source `the November 2 reference manuscript`
lines 3346-3352 (outer semigroup `S_ε`, its heat factor `e^{νε²(e^t-1)Δ_x}`), 1339-1362
(`L = 𝒯 - νΔ - 1/2`).

Route (Duhamel twice, then Minkowski in `X`):
for `θ > 0`, on a smooth phase test `ψ` with `W` the representative of `Δ²ψ`
(`Δ = lapT`),
`e^{θΔ}ψ - ψ - θΔψ = ∫_0^θ ∫_0^t e^{sΔ}Δ²ψ ds dt` pointwise (twice the heat FTC
`Heat.average_sub_eq_integral`, `Lib/HeatR3/FTC.lean:279`), and the `X`-norm of the right side is
`≤ θ²/2 · ‖W‖` (`eLpNorm_heatConv_le`, Minkowski's integral inequality).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- The function on the phase space `PSpace P` of the cell function `g(τ, x)`
(as in `OuterRepFn`). -/
def cellFn {P : ℝ} [Fact (0 < P)] (g : ℝ × Space → UnforcedLeray.B0223.SpaceC) :
    UnforcedLeray.B0223.PSpace P → UnforcedLeray.B0223.SpaceC :=
  fun z => g ((UnforcedLeray.B0223.toCell P z).2, (UnforcedLeray.B0223.toCell P z).1)

/-- **Minkowski step** (source 3346-3352; Minkowski's integral inequality in `X = L²(PSpace)`
and the contraction `Heat.eLpNorm_heatConv_le`).  If `R ∈ X` is a.e. the double heat integral
`∫_0^θ ∫_0^t e^{sΔ}W ds dt` of `W ∈ X` (`heatConv (ιx P) s ↑W`, pointwise Bochner integrals),
then `‖R‖ ≤ θ²/2 ‖W‖`; here `w` is a measurable function a.e. equal to `W`
(heat integrals of `w` are used, not of the class `W`, which would only be a.e. defined).  Proof sketch: `(s, z) ↦ heatConv (ιx P) s W z` is jointly measurable on
`(0,∞) × PSpace` (integrand `(s,z,y) ↦ gaussKernel 3 s y • W (z - ιx y)` is measurable, then
`StronglyMeasurable.integral_prod_right`), apply Minkowski's integral inequality
(`PlanarBS.Conv.eLpNorm_integral_le`, `Lib/Kernels/PlanarBS/P/Infra/ConvMinkowski/Minkowski.lean:214`,
or Mathlib's `MeasureTheory.eLpNorm_integral_le...`) twice (in `s` and in `t`) with
`eLpNorm_heatConv_le` (`Lib/HeatR3/ConvOp.lean:223`), `∫_0^θ ∫_0^t 1 = θ²/2`. -/
def ODHT_Mink : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (θ : ℝ), 0 < θ → ∀ (W R : UnforcedLeray.B0223.X
      UnforcedLeray.B0223.SpaceC P) (w : UnforcedLeray.B0223.PSpace P → UnforcedLeray.B0223.SpaceC),
    Measurable w →
    (W : UnforcedLeray.B0223.PSpace P → UnforcedLeray.B0223.SpaceC) =ᵐ[volume] w →
    ((R : UnforcedLeray.B0223.PSpace P → UnforcedLeray.B0223.SpaceC) =ᵐ[volume]
      fun z => ∫ t in (0 : ℝ)..θ, ∫ s in (0 : ℝ)..t,
        UnforcedLeray.Heat.heatConv (UnforcedLeray.B0223.ιx P) s w z) →
    ‖R‖ ≤ θ ^ 2 / 2 * ‖W‖

/-- **Pointwise double Duhamel on a smooth phase test** (source 3346-3352, 1339-1362).  For
`θ > 0` and every `z = (x, τ)`, with `u = cellFn ψ` etc.:
`heatConv θ u z - u z - θ • (cellFn (lapT ψ)) z
  = ∫_0^θ ∫_0^t heatConv s (cellFn (lapT (lapT ψ))) z ds dt`.
Proof: `heatConv (ιx P) s (cellFn g) z = Heat.average s (fun y => g (τ, y)) x`
(`Heat.heatConv_space_eq_average`, `toCell (x - y, τ) = ...`), slice Laplacian
`PartIIa.HeatGaussEquationAux.lapT_eq_vlap_slice`
(`Short/PartII-a/Tasks/F05aAdjResolventSolution/HeatGaussEquation.lean:206`), and
`Heat.average_sub_eq_integral` (`Lib/HeatR3/FTC.lean:279`) applied to the slice of `ψ` and to
the slice of `lapT ψ` (uniform bounds on `iteratedFDeriv ℝ k` for `k ≤ 2` from the compact
support in `x` and periodicity in `τ`, as in `odExists`). -/
def ODHT_Pointwise : Prop :=
  ∀ (p : Params) (ψ : ℝ × Space → CVec3), IsPhaseTest p.period ψ →
    ∀ θ : ℝ, 0 < θ → ∀ z : UnforcedLeray.B0223.PSpace p.period,
      UnforcedLeray.Heat.heatConv (UnforcedLeray.B0223.ιx p.period) θ (cellFn ψ) z
        - cellFn ψ z - θ • cellFn (lapT ψ) z
      = ∫ t in (0 : ℝ)..θ, ∫ s in (0 : ℝ)..t,
          UnforcedLeray.Heat.heatConv (UnforcedLeray.B0223.ιx p.period) s
            (cellFn (lapT (lapT ψ))) z

/-- **Joint measurability of the heat integral** (`(s, z) ↦ ∫ G_s(y) • w(z - ιx y) dy`).
Proof: `(s, z, y) ↦ gaussKernel 3 s y • w (z - ιx y)` is measurable, then
`MeasureTheory.StronglyMeasurable.integral_prod_right'`. -/
def ODHT_JointMeas : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (w : UnforcedLeray.B0223.PSpace P → UnforcedLeray.B0223.SpaceC),
    Measurable w → Measurable (fun q : ℝ × UnforcedLeray.B0223.PSpace P =>
      UnforcedLeray.Heat.heatConv (UnforcedLeray.B0223.ιx P) q.1 w q.2)

/-- **Bridge from `PSpace` to a slice**: the cell heat integral at `z = (x, ·)` of `cellFn g`
is the `ℝ³` heat average of the slice `g(τ, ·)` at `x`, `(x, τ) = toCell z`
(`Heat.heatConv_space_eq_average` after unfolding `heatConv`, `ιx = inl`; `toCell (z - ιx y)
= ((toCell z).1 - y, (toCell z).2)` by definition of `toCell`, `Lift.lean:40`). -/
def ODHT_Bridge : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (g : ℝ × Space → UnforcedLeray.B0223.SpaceC) (s : ℝ)
    (z : UnforcedLeray.B0223.PSpace P),
    UnforcedLeray.Heat.heatConv (UnforcedLeray.B0223.ιx P) s (cellFn g) z
      = UnforcedLeray.Heat.average s
          (fun y : Space => g ((UnforcedLeray.B0223.toCell P z).2, y))
          (UnforcedLeray.B0223.toCell P z).1

/-- **Uniform slice bounds of a phase test**: smooth, `x`-support in `‖x‖ ≤ R`, `τ`-periodic, so
all derivatives of order `≤ 2` of the slices `g(τ, ·)` are uniformly bounded (compactness of
`[0,P] × closedBall 0 R`, periodicity; the same argument as in `odExists`, applied to
`iteratedFDeriv ℝ k (fun y => g (τ, y))` via `PartIIa` lemma `slice_iteratedFDeriv_eq`). -/
def ODHT_SliceBounds : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (g : ℝ × Space → CVec3), IsPhaseTest P g →
    ∃ M : ℝ, ∀ τ : ℝ, ∀ k : ℕ, k ≤ 2 → ∀ x : Space,
      ‖iteratedFDeriv ℝ k (fun y : Space => g (τ, y)) x‖ ≤ M

/-- **Double heat Duhamel on `ℝ³`** (twice `Heat.average_sub_eq_integral`,
`Lib/HeatR3/FTC.lean:279`, first for `u`, then for `vlap u`, then `intervalIntegral` algebra):
`e^{θΔ}u - u - θΔu = ∫_0^θ ∫_0^t e^{sΔ}Δ²u ds dt` at every point. -/
def ODHT_SliceDuhamel : Prop :=
  ∀ (u : Space → CVec3) (M : ℝ), ContDiff ℝ ∞ u →
    (∀ k : ℕ, k ≤ 2 → ∀ x : Space, ‖iteratedFDeriv ℝ k u x‖ ≤ M) →
    (∀ k : ℕ, k ≤ 2 → ∀ x : Space, ‖iteratedFDeriv ℝ k (UnforcedLeray.Heat.vlap u) x‖ ≤ M) →
    ∀ θ : ℝ, 0 < θ → ∀ x : Space,
      UnforcedLeray.Heat.average θ u x - u x - θ • UnforcedLeray.Heat.vlap u x
      = ∫ t in (0 : ℝ)..θ, ∫ s in (0 : ℝ)..t,
          UnforcedLeray.Heat.average s (UnforcedLeray.Heat.vlap (UnforcedLeray.Heat.vlap u)) x

theorem odhtPointwise_of (hB : ODHT_Bridge) (hS : ODHT_SliceBounds) (hD : ODHT_SliceDuhamel) :
    ODHT_Pointwise := by
  intro p ψ hψ θ hθ z
  have : Fact (0 < p.period) := ⟨p.period_pos⟩
  obtain ⟨M1, hM1⟩ := hS p.period ψ hψ
  obtain ⟨M2, hM2⟩ := hS p.period _ hψ.lapT
  have hsm : ∀ τ : ℝ, ContDiff ℝ ∞ (fun y : Space => ψ (τ, y)) := fun τ =>
    hψ.smooth.comp (contDiff_const.prodMk contDiff_id)
  have hv : ∀ τ : ℝ, UnforcedLeray.Heat.vlap (fun y : Space => ψ (τ, y))
      = fun y => lapT ψ (τ, y) := fun τ => by
    funext y
    exact (UnforcedLeray.Short.PartIIa.HeatGaussEquationAux.lapT_eq_vlap_slice hψ.smooth τ y).symm
  have hv2 : ∀ τ : ℝ, UnforcedLeray.Heat.vlap (UnforcedLeray.Heat.vlap
      (fun y : Space => ψ (τ, y))) = fun y => lapT (lapT ψ) (τ, y) := fun τ => by
    rw [hv τ]
    funext y
    exact (UnforcedLeray.Short.PartIIa.HeatGaussEquationAux.lapT_eq_vlap_slice
      hψ.lapT.smooth τ y).symm
  set τ := (UnforcedLeray.B0223.toCell p.period z).2 with hτ
  set x := (UnforcedLeray.B0223.toCell p.period z).1 with hx
  have key := hD (fun y : Space => ψ (τ, y)) (max M1 M2) (hsm τ)
    (fun k hk y => (hM1 τ k hk y).trans (le_max_left _ _))
    (fun k hk y => by rw [hv τ]; exact (hM2 τ k hk y).trans (le_max_right _ _)) θ hθ x
  rw [hv2 τ, hv τ] at key
  have e1 := hB p.period ψ θ z
  have e0 : cellFn ψ z = ψ (τ, x) := rfl
  have e2 : cellFn (lapT ψ) z = lapT ψ (τ, x) := rfl
  rw [e1, e0, e2]
  have e3 : ∀ s, UnforcedLeray.Heat.heatConv (UnforcedLeray.B0223.ιx p.period) s
      (cellFn (lapT (lapT ψ))) z = UnforcedLeray.Heat.average s
        (fun y => lapT (lapT ψ) (τ, y)) x := fun s => hB p.period _ s z
  simp_rw [e3]
  exact key

theorem odHeatTaylor_of (hM : ODHT_Mink) (hT : ODHT_Pointwise) : OD_HeatTaylor := by
  intro p ψ hψ Ψ ΨΔ hΨ hΔ
  have : Fact (0 < p.period) := ⟨p.period_pos⟩
  obtain ⟨W, hW⟩ := odExists p _ hψ.lapT.lapT
  refine ⟨‖W‖ / 2, by positivity, fun θ h0 _ => ?_⟩
  rcases h0.eq_or_lt with h | hpos
  · subst h
    rw [UnforcedLeray.B0223.heatC_of_nonpos le_rfl]
    simp
  · have hι := UnforcedLeray.B0223.continuous_ιx (P := p.period)
    have hΨ' : (Ψ : UnforcedLeray.B0223.PSpace p.period → UnforcedLeray.B0223.SpaceC)
        =ᵐ[volume] cellFn ψ := hΨ
    have hΔ' : (ΨΔ : UnforcedLeray.B0223.PSpace p.period → UnforcedLeray.B0223.SpaceC)
        =ᵐ[volume] cellFn (lapT ψ) := hΔ
    have hW' : (W : UnforcedLeray.B0223.PSpace p.period → UnforcedLeray.B0223.SpaceC)
        =ᵐ[volume] cellFn (lapT (lapT ψ)) := hW
    have hwm : Measurable (cellFn (P := p.period) (lapT (lapT ψ))) := by
      refine (hψ.lapT.lapT.smooth.continuous.measurable).comp ?_
      exact (measurable_snd.comp (UnforcedLeray.B0223.measurable_toCell (P := p.period))).prodMk
        (measurable_fst.comp (UnforcedLeray.B0223.measurable_toCell (P := p.period)))
    have hR : ((UnforcedLeray.B0223.heatC (E := UnforcedLeray.B0223.SpaceC) θ Ψ - Ψ
          - (θ : ℂ) • ΨΔ : UnforcedLeray.B0223.X UnforcedLeray.B0223.SpaceC p.period) :
        UnforcedLeray.B0223.PSpace p.period → UnforcedLeray.B0223.SpaceC)
        =ᵐ[volume] fun z => ∫ t in (0 : ℝ)..θ, ∫ s in (0 : ℝ)..t,
          UnforcedLeray.Heat.heatConv (UnforcedLeray.B0223.ιx p.period) s
            (cellFn (lapT (lapT ψ))) z := by
      have h1 := UnforcedLeray.B0223.heatC_rep hpos Ψ
      have h2 := UnforcedLeray.Heat.heatConv_congr_ae (UnforcedLeray.B0223.ιx p.period)
        hι.measurable θ hΨ'
      filter_upwards [Lp.coeFn_sub (UnforcedLeray.B0223.heatC (E := UnforcedLeray.B0223.SpaceC)
          θ Ψ - Ψ) ((θ : ℂ) • ΨΔ), Lp.coeFn_sub
          (UnforcedLeray.B0223.heatC (E := UnforcedLeray.B0223.SpaceC) θ Ψ) Ψ,
        Lp.coeFn_smul (θ : ℂ) ΨΔ, h1, h2, hΨ', hΔ'] with z a1 a2 a3 a4 a5 a6 a7
      rw [a1, Pi.sub_apply, a2, Pi.sub_apply, a3, Pi.smul_apply, a4, a5, a6, a7,
        Complex.coe_smul]
      exact hT p ψ hψ θ hpos z
    have := hM p.period θ hpos W _ _ hwm hW' hR
    calc _ ≤ θ ^ 2 / 2 * ‖W‖ := this
      _ = ‖W‖ / 2 * θ ^ 2 := by ring

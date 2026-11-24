import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_3_2_1_2

/-!
# Part III-a, `PartIII-a:T21/3/2/1/2/1`: `UnitHeatDuality` (lemma A) from three lemmas

Source of record: `the November 2 reference manuscript`, lines 2819-2836
(cell pairing of the Gaussian flow of the lift against a periodic test equals the pairing of the
lift against the real heat flow of the test).

With `G = heatKernel2 τ` (even), `F = (xColumnHeatLift _ w).1` and the kernel
`K z y = G(z-y) F(y) φ(z)`, both sides are iterated integrals of `K` over (cell × plane),
resp. (plane × cell); they agree by the diagonal translation invariance of `K` (`q`-periodicity
of `F`, `φ`).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory

namespace UnforcedLeray.Short.IIIa.Exist

open UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

/-- Mass transport / unfolding on the cylinder: a measurable kernel on the plane that is
invariant under the diagonal translation `(z, y) ↦ (z + (c,0), y + (c,0))` and integrable on
`cell × plane` has equal iterated integrals over `cell × plane` and `plane × cell`.
Proof sketch: tile the plane by the translates `cell + (kc,0)` of the fundamental domain,
`∫_{z∈cell}∫_{y∈cell+k} K = ∫_{z∈cell-k}∫_{y∈cell} K` by diagonal invariance, and sum over `k`
(Tonelli for `|K|`, then dominated `tsum`/`integral_iUnion`). -/
def MassTransport : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ K : ℝ × ℝ → ℝ × ℝ → ℝ,
    Integrable (Function.uncurry K) ((volume.restrict (UnforcedLeray.B0579.cell c)).prod volume) →
    (∀ z y : ℝ × ℝ, K (z.1 + c, z.2) (y.1 + c, y.2) = K z y) →
    ∫ z in UnforcedLeray.B0579.cell c, ∫ y, K z y =
      ∫ y in UnforcedLeray.B0579.cell c, ∫ z, K z y

/-- The duality kernel is integrable on `cell × plane`: for bounded `φ` and `q`-periodic `F`
integrable on the cell, `∫_{z∈cell}∫_y G(z-y)|F(y)| = ∫ G · ∫_{cell}|F(z-u)| dz du =
‖F‖_{L¹(cell)}` (periodicity of `F` makes `∫_{cell}|F(· - u)|` independent of `u`). -/
def DualityKernelIntegrable : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ τ : ℝ, 0 < τ → ∀ F φ : ℝ × ℝ → ℝ, Measurable F →
    (∀ z : ℝ × ℝ, F (z.1 + c, z.2) = F z) → IntegrableOn F (UnforcedLeray.B0579.cell c) →
    Measurable φ → ∀ M : ℝ, (∀ z, |φ z| ≤ M) →
      Integrable (Function.uncurry fun z y : ℝ × ℝ =>
          UnforcedLeray.B0284.heatKernel2 τ (z - y) * F y * φ z)
        ((volume.restrict (UnforcedLeray.B0579.cell c)).prod volume)

/-- The first component of `heat τ` of a first-component lift is the real heat convolution of
its first component. -/
def HeatLiftFst : Prop :=
  ∀ τ : ℝ, 0 < τ → ∀ (F : ℝ × ℝ → ℝ) (z : ℝ × ℝ),
    (UnforcedLeray.B0284.heat τ (fun z => (F z, 0)) z).1 =
      ∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 τ w * F (z - w)

theorem unitHeatDuality_of (hM : MassTransport) (hI : DualityKernelIntegrable)
    (hH : HeatLiftFst)
    (hG : LapTestBounded) : UnitHeatDuality := by
  intro c m _ hm w φ hφ τ hτ
  have hc : 0 < c := Fact.out
  set F : ℝ × ℝ → ℝ := fun y => (xColumnHeatLift hc w y).1 with hF
  have hFper : ∀ z : ℝ × ℝ, F (z.1 + c, z.2) = F z := fun z => by
    have := periodic_xColumnHeatLift hc w z
    simpa [hF] using congrArg Prod.fst this
  have hFmeas : Measurable F :=
    (stronglyMeasurable_xColumnHeatLift hc w).measurable.fst
  have hFint : IntegrableOn F (UnforcedLeray.B0579.cell c) := by
    have := integrable_xColumnPeriodicRep hc hm w
    have hleft : -(c / 2) = -c / 2 := by ring
    simpa [hF, xColumnHeatLift, UnforcedLeray.B0579.cell, UnforcedLeray.Cyl.cell,
      UnforcedLeray.Cyl.cellμ, IntegrableOn, hleft] using this
  obtain ⟨_, ⟨M, hM0⟩, _⟩ := hG c hc φ hφ
  have hφm : Measurable φ := hφ.continuous.measurable
  have hGsymm : ∀ u : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 τ (-u) =
      UnforcedLeray.B0284.heatKernel2 τ u := by
    intro u
    simp [UnforcedLeray.B0284.heatKernel2, UnforcedLeray.B0191.heatKernel]
  set K : ℝ × ℝ → ℝ × ℝ → ℝ := fun z y =>
    UnforcedLeray.B0284.heatKernel2 τ (z - y) * F y * φ z with hK
  have hKint := hI c hc τ hτ F φ hFmeas hFper hFint hφm M hM0
  have hKper : ∀ z y : ℝ × ℝ, K (z.1 + c, z.2) (y.1 + c, y.2) = K z y := by
    intro z y
    simp only [hK]
    have h1 : ((z.1 + c, z.2) : ℝ × ℝ) - (y.1 + c, y.2) = z - y := by
      ext <;> simp
    rw [h1, hFper y, hφ.periodic z]
  have key := hM c hc K hKint hKper
  have hL : ∀ z : ℝ × ℝ,
      (UnforcedLeray.B0284.heat τ (xColumnHeatLift hc w) z).1 * φ z = ∫ y, K z y := by
    intro z
    have h0 := hH τ hτ F z
    have h1 : (UnforcedLeray.B0284.heat τ (xColumnHeatLift hc w) z).1 =
        ∫ y, UnforcedLeray.B0284.heatKernel2 τ (z - y) * F y := by
      have : xColumnHeatLift hc w = fun z => (F z, 0) := rfl
      rw [this, h0]
      rw [← integral_sub_left_eq_self (fun y : ℝ × ℝ =>
        UnforcedLeray.B0284.heatKernel2 τ (z - y) * F y) volume z]
      congr 1; funext u; simp
    rw [h1, ← integral_mul_const]
  have hR : ∀ y : ℝ × ℝ, F y * realHeat τ φ y = ∫ z, K z y := by
    intro y
    have h1 : realHeat τ φ y = ∫ z, UnforcedLeray.B0284.heatKernel2 τ (z - y) * φ z := by
      unfold realHeat
      rw [← integral_sub_left_eq_self (fun z : ℝ × ℝ =>
        UnforcedLeray.B0284.heatKernel2 τ (z - y) * φ z) volume y]
      congr 1; funext u
      have : y - u - y = -u := by abel
      simp [this, hGsymm]
    rw [h1, ← integral_const_mul]
    congr 1; funext z; simp only [hK]; ring
  calc _ = ∫ z in UnforcedLeray.B0579.cell c, ∫ y, K z y := by
        congr 1; funext z; exact hL z
    _ = ∫ y in UnforcedLeray.B0579.cell c, ∫ z, K z y := key
    _ = _ := by congr 1; funext y; exact (hR y).symm
end UnforcedLeray.Short.IIIa.Exist

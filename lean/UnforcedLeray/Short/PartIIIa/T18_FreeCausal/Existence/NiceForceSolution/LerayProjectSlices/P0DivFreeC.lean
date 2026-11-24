import UnforcedLeray.Short.PartIIIa.Sub.T18_2_4_2
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.LerayProjectSlices.TestBridge

/-!
# Part III-a, leaf `PartIII-a:T18/2/4/2/4`: `𝒫₀ f` is divergence free against `B0579` tests

Target (`Sub/T18_2_4_2.lean`): `P0DivFreeC`. Source of record:
`the November 2 reference manuscript`, lines 3442-3465.

Proof: the real and imaginary parts `P0re c f`, `P0im c f` are in `divFree c` (`Cyl.P0_mem`).
For such a class `g` and a test `ψ`, `Cyl.mem_divFree` gives `⟪gradL ψ, g⟫ = 0`; the test bridge
identifies `B0579.pd j ψ` with `Cyl.partialQ`, `Cyl.partialEta`. The complex integrand splits into
the real pairings `A + i B` (integrable, since `⟪gradL ψ, g⟫` is an `L²` inner product).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.IIIa

/-- `⟪gradT ψ z, w⟫ = w₀ ∂_q ψ + w₁ ∂_η ψ`. -/
theorem inner_gradT_aux_p0div (ψ : ℝ × ℝ → ℝ) (z : ℝ × ℝ) (w : UnforcedLeray.Cyl.Vec2) :
    ⟪UnforcedLeray.Cyl.gradT ψ z, w⟫_ℝ =
      w 0 * UnforcedLeray.Cyl.partialQ ψ z + w 1 * UnforcedLeray.Cyl.partialEta ψ z := by
  rw [real_inner_comm _ _]
  unfold UnforcedLeray.Cyl.gradT
  rw [UnforcedLeray.Cyl.inner_vec]

/-- Real pairing of a divergence-free class with a test gradient: integrable, and of integral
zero against `cellμ`. -/
theorem pairInt_aux_p0div (c : ℝ) (g : UnforcedLeray.Cyl.L2v c)
    (hg : g ∈ UnforcedLeray.Cyl.divFree c) (ψ : ℝ × ℝ → ℝ) (hψ : B0579.IsCylTest c ψ) :
    Integrable (fun x : ℝ × ℝ => (g : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) x 0 * B0579.pd 0 ψ x +
        (g : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) x 1 * B0579.pd 1 ψ x) (UnforcedLeray.Cyl.cellμ c) ∧
      ∫ x, ((g : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) x 0 * B0579.pd 0 ψ x +
        (g : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) x 1 * B0579.pd 1 ψ x) ∂(UnforcedLeray.Cyl.cellμ c) = 0 := by
  have hb := (testBridge c ψ).1.mp hψ
  have hS : UnforcedLeray.Sob.IsCylTest c ψ := hb
  have hpd := (testBridge c ψ).2 hψ
  have hae : (fun x => ⟪UnforcedLeray.Cyl.gradL hS x, g x⟫_ℝ) =ᵐ[UnforcedLeray.Cyl.cellμ c]
      fun x => (g : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) x 0 * B0579.pd 0 ψ x +
        (g : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) x 1 * B0579.pd 1 ψ x := by
    filter_upwards [(UnforcedLeray.Cyl.memLp_gradT hS).coeFn_toLp] with x hx
    have hx' : UnforcedLeray.Cyl.gradL hS x = UnforcedLeray.Cyl.gradT ψ x := hx
    rw [hx', inner_gradT_aux_p0div, (hpd x).1, (hpd x).2]
  have hm := (UnforcedLeray.Cyl.mem_divFree.1 hg) ψ hS
  rw [L2.inner_def] at hm
  refine ⟨(L2.integrable_inner (UnforcedLeray.Cyl.gradL hS) g).congr hae, ?_⟩
  exact (integral_congr_ae hae.symm).trans hm

theorem p0DivFreeC : UnforcedLeray.Short.IIIa.P0DivFreeC := by
  unfold UnforcedLeray.Short.IIIa.P0DivFreeC
  intro c _hc f ψ hψ
  rw [← cellμ_eq c]
  have hm1 : UnforcedLeray.Short.IIIa.P0re c f ∈ UnforcedLeray.Cyl.divFree c :=
    UnforcedLeray.Cyl.P0_mem _
  have hm2 : UnforcedLeray.Short.IIIa.P0im c f ∈ UnforcedLeray.Cyl.divFree c :=
    UnforcedLeray.Cyl.P0_mem _
  obtain ⟨hI1, hZ1⟩ := pairInt_aux_p0div c _ hm1 ψ hψ
  obtain ⟨hI2, hZ2⟩ := pairInt_aux_p0div c _ hm2 ψ hψ
  have hpt : ∀ x : ℝ × ℝ,
      UnforcedLeray.Short.IIIa.P0C c f x 0 * ((B0579.pd 0 ψ x : ℝ) : ℂ) +
          UnforcedLeray.Short.IIIa.P0C c f x 1 * ((B0579.pd 1 ψ x : ℝ) : ℂ) =
        ((((UnforcedLeray.Short.IIIa.P0re c f : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) x 0 *
            B0579.pd 0 ψ x + (UnforcedLeray.Short.IIIa.P0re c f : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) x 1 *
            B0579.pd 1 ψ x : ℝ) : ℂ)) +
          Complex.I * ((((UnforcedLeray.Short.IIIa.P0im c f : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) x 0 *
            B0579.pd 0 ψ x + (UnforcedLeray.Short.IIIa.P0im c f : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) x 1 *
            B0579.pd 1 ψ x : ℝ) : ℂ)) := by
    intro x
    simp only [UnforcedLeray.Short.IIIa.P0C, UnforcedLeray.Short.IIIa.cplxOf]
    push_cast
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_add, integral_const_mul]
  · simp only [integral_complex_ofReal, hZ1, hZ2]
    simp
  all_goals first
    | exact Integrable.ofReal hI1
    | exact (Integrable.ofReal hI2).const_mul _

end UnforcedLeray.Short.IIIa

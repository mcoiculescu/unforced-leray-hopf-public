import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T12_1_3_1_5

/-!


Source: `the November 2 reference manuscript` lines 1670, 1923-1926.
Fubini (`integral_integral_swap`) plus the cell shift reduce `CylMollSwapDiv` to three analytic
facts about a `c`-periodic `L^r(avgμ c)` field `D`, a bump `ρ`, and a "good" weight `g` (continuous,
`c`-periodic in `q`, vanishing for `|η| > L`; `g = ∂_q φ`, `∂_η φ` for a `CylTest φ`):

* `CylSwapInt1`: `(z, y) ↦ ρ(y) D_i(z - y) g(z)` is integrable for `avgμ c ⊗ volume`;
* `CylSwapInt2`: `(u, y) ↦ D_i(u) ρ(y) g(u + y)` is integrable for `avgμ c ⊗ volume`;
* `CylMollComp`: the vector-valued mollification `cylMoll ρ D z` has `i`-th component
  `∫ ρ(y) D_i(z - y) dy` (Bochner integral commutes with the coordinate functional; integrability
  from local integrability of `D`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Complex
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

namespace Swap

/-- Cell shift on the averaged measure: `∫_{avgμ} G(z - y) = ∫_{avgμ} G` for periodic `G`. -/
theorem avg_integral_comp_sub {c : ℝ} (hc : 0 < c) {G : ℝ × ℝ → ℂ}
    (hG : UnforcedLeray.Cyl.IsPeriodic c G) (y : ℝ × ℝ) :
    ∫ z, G (z - y) ∂(UnforcedLeray.Cyl.avgμ c) = ∫ z, G z ∂(UnforcedLeray.Cyl.avgμ c) := by
  have key : ∫ z, G (z - y) ∂(UnforcedLeray.Cyl.cellμ c)
      = ∫ z, G z ∂(UnforcedLeray.Cyl.cellμ c) := by
    unfold UnforcedLeray.Cyl.cellμ
    simp only [sub_eq_add_neg]
    exact UnforcedLeray.Cyl.integral_cell_comp_add hc hG (-y)
  unfold UnforcedLeray.Cyl.avgμ
  rw [integral_smul_measure, integral_smul_measure, key]

/-- `∇φ` is `c`-periodic in `q` for a cylinder test `φ`. -/
theorem fderiv_periodic_of {c : ℝ} {φ : ℝ × ℝ → ℝ} (hφ : UnforcedLeray.Short.IIb.CylTest c φ)
    (w : ℝ × ℝ) : fderiv ℝ φ (w.1 + c, w.2) = fderiv ℝ φ w := by
  have hw : ((w.1 + c, w.2) : ℝ × ℝ) = w + (c, 0) := by ext <;> simp
  have hfun : (fun x : ℝ × ℝ => φ (x + (c, 0))) = φ := by
    funext x
    show φ (x + (c, 0)) = φ x
    rw [← hφ.periodic x]
    congr 1
    ext <;> simp
  calc fderiv ℝ φ (w.1 + c, w.2) = fderiv ℝ φ (w + (c, 0)) := by rw [hw]
    _ = fderiv ℝ (fun x : ℝ × ℝ => φ (x + (c, 0))) w := (fderiv_comp_add_right _).symm
    _ = fderiv ℝ φ w := by rw [hfun]

/-- `∇φ` vanishes outside a slab `|η| ≤ L` for a cylinder test `φ`. -/
theorem fderiv_zero_of_far {c : ℝ} {φ : ℝ × ℝ → ℝ} (hφ : UnforcedLeray.Short.IIb.CylTest c φ) :
    ∃ L : ℝ, ∀ z : ℝ × ℝ, L < |z.2| → fderiv ℝ φ z = 0 := by
  obtain ⟨L, hL⟩ := hφ.bounded
  refine ⟨L, fun z hz => ?_⟩
  have hopen : IsOpen {w : ℝ × ℝ | L < |w.2|} :=
    isOpen_lt continuous_const (continuous_snd.abs)
  have hev : φ =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
    filter_upwards [hopen.mem_nhds hz] with w hw
    exact hL w hw
  rw [hev.fderiv_eq]
  simp

/-- One component of the mollified weak divergence identity, reduced to Fubini and the cell
shift. The two product integrability facts are the remaining analytic inputs. -/
theorem swap_component {c : ℝ} (hc : 0 < c) (D : ℝ × ℝ → CMerid)
    (hD : UnforcedLeray.Cyl.IsPeriodic c D) (i : Fin 2)
    (ρ : ContDiffBump (0 : ℝ × ℝ)) (g : ℝ × ℝ → ℝ) (hg : UnforcedLeray.Cyl.IsPeriodic c g)
    (int1 : Integrable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
        ((ρ.normed volume p.2 : ℝ) : ℂ) * D (p.1 - p.2) i * ((g p.1 : ℝ) : ℂ))
        ((UnforcedLeray.Cyl.avgμ c).prod volume))
    (int2 : Integrable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
        D p.1 i * ((ρ.normed volume p.2 * g (p.1 + p.2) : ℝ) : ℂ))
        ((UnforcedLeray.Cyl.avgμ c).prod volume)) :
    ∫ z, (∫ y, ((ρ.normed volume y : ℝ) : ℂ) * D (z - y) i) * ((g z : ℝ) : ℂ)
        ∂(UnforcedLeray.Cyl.avgμ c)
      = ∫ u, D u i * ((∫ y, ρ.normed volume y * g (u + y) : ℝ) : ℂ)
        ∂(UnforcedLeray.Cyl.avgμ c) := by
  haveI : SFinite (UnforcedLeray.Cyl.avgμ c) := by
    unfold UnforcedLeray.Cyl.avgμ UnforcedLeray.Cyl.cellμ
    infer_instance
  -- the shifted integrand is periodic
  have hGper : ∀ y : ℝ × ℝ,
      UnforcedLeray.Cyl.IsPeriodic c (fun u => D u i * ((g (u + y) : ℝ) : ℂ)) := by
    intro y w
    show D (w.1 + c, w.2) i * ((g ((w.1 + c, w.2) + y) : ℝ) : ℂ)
      = D w i * ((g (w + y) : ℝ) : ℂ)
    have e : ((w.1 + c, w.2) : ℝ × ℝ) + y = ((w + y).1 + c, (w + y).2) := by
      ext <;> simp <;> ring
    rw [hD w, e, hg (w + y)]
  -- step 1: pull the inner integral out as an integral of the product
  have step1 : ∀ z : ℝ × ℝ,
      (∫ y, ((ρ.normed volume y : ℝ) : ℂ) * D (z - y) i) * ((g z : ℝ) : ℂ)
        = ∫ y, ((ρ.normed volume y : ℝ) : ℂ) * D (z - y) i * ((g z : ℝ) : ℂ) :=
    fun z => (integral_mul_const _ _).symm
  -- step 2: per-`y` cell shift
  have step3 : ∀ y : ℝ × ℝ,
      ∫ z, ((ρ.normed volume y : ℝ) : ℂ) * D (z - y) i * ((g z : ℝ) : ℂ)
          ∂(UnforcedLeray.Cyl.avgμ c)
        = ((ρ.normed volume y : ℝ) : ℂ) *
          ∫ u, D u i * ((g (u + y) : ℝ) : ℂ) ∂(UnforcedLeray.Cyl.avgμ c) := by
    intro y
    have hsh := avg_integral_comp_sub hc (hGper y) y
    simp only [sub_add_cancel] at hsh
    rw [← hsh, ← integral_const_mul]
    simp only [mul_assoc, integral_const_mul]
  -- step 3: the right-hand side, Fubini on `int2`
  have step4 : ∀ u : ℝ × ℝ,
      D u i * ((∫ y, ρ.normed volume y * g (u + y) : ℝ) : ℂ)
        = ∫ y, D u i * ((ρ.normed volume y * g (u + y) : ℝ) : ℂ) := by
    intro u
    have h : ((∫ y, ρ.normed volume y * g (u + y) : ℝ) : ℂ)
        = ∫ y, ((ρ.normed volume y * g (u + y) : ℝ) : ℂ) := integral_ofReal.symm
    rw [h, ← integral_const_mul]
  have step5 : ∀ y : ℝ × ℝ,
      ∫ u, D u i * ((ρ.normed volume y * g (u + y) : ℝ) : ℂ) ∂(UnforcedLeray.Cyl.avgμ c)
        = ((ρ.normed volume y : ℝ) : ℂ) *
          ∫ u, D u i * ((g (u + y) : ℝ) : ℂ) ∂(UnforcedLeray.Cyl.avgμ c) := by
    intro y
    have h : ∀ u : ℝ × ℝ, D u i * ((ρ.normed volume y * g (u + y) : ℝ) : ℂ)
        = ((ρ.normed volume y : ℝ) : ℂ) * (D u i * ((g (u + y) : ℝ) : ℂ)) := by
      intro u
      push_cast
      ring
    simp only [h, integral_const_mul]
  calc ∫ z, (∫ y, ((ρ.normed volume y : ℝ) : ℂ) * D (z - y) i) * ((g z : ℝ) : ℂ)
          ∂(UnforcedLeray.Cyl.avgμ c)
      = ∫ z, ∫ y, ((ρ.normed volume y : ℝ) : ℂ) * D (z - y) i * ((g z : ℝ) : ℂ) ∂volume
          ∂(UnforcedLeray.Cyl.avgμ c) := integral_congr_ae (Eventually.of_forall step1)
    _ = ∫ y, ∫ z, ((ρ.normed volume y : ℝ) : ℂ) * D (z - y) i * ((g z : ℝ) : ℂ)
          ∂(UnforcedLeray.Cyl.avgμ c) ∂volume :=
        integral_integral_swap
          (f := fun z y => ((ρ.normed volume y : ℝ) : ℂ) * D (z - y) i * ((g z : ℝ) : ℂ)) int1
    _ = ∫ y, ((ρ.normed volume y : ℝ) : ℂ) *
          ∫ u, D u i * ((g (u + y) : ℝ) : ℂ) ∂(UnforcedLeray.Cyl.avgμ c) ∂volume :=
        integral_congr_ae (Eventually.of_forall step3)
    _ = ∫ y, ∫ u, D u i * ((ρ.normed volume y * g (u + y) : ℝ) : ℂ)
          ∂(UnforcedLeray.Cyl.avgμ c) ∂volume :=
        integral_congr_ae (Eventually.of_forall fun y => (step5 y).symm)
    _ = ∫ u, ∫ y, D u i * ((ρ.normed volume y * g (u + y) : ℝ) : ℂ) ∂volume
          ∂(UnforcedLeray.Cyl.avgμ c) :=
        (integral_integral_swap
          (f := fun u y => D u i * ((ρ.normed volume y * g (u + y) : ℝ) : ℂ)) int2).symm
    _ = ∫ u, D u i * ((∫ y, ρ.normed volume y * g (u + y) : ℝ) : ℂ)
          ∂(UnforcedLeray.Cyl.avgμ c) :=
        integral_congr_ae (Eventually.of_forall fun u => (step4 u).symm)

end Swap

/-- A weight `g` allowed in the mollified weak divergence: continuous, `c`-periodic in `q`, and
vanishing outside a slab `|η| ≤ L` (e.g. `∂_q φ`, `∂_η φ` for a `CylTest φ`). -/
def SwapGood (c : ℝ) (g : ℝ × ℝ → ℝ) : Prop :=
  Continuous g ∧ UnforcedLeray.Cyl.IsPeriodic c g ∧ ∃ L : ℝ, ∀ z : ℝ × ℝ, L < |z.2| → g z = 0

/-- **Leaf `T12/1/3/1/5/3/1`** (SP 1923-1926): integrability of `ρ(y) D_i(z-y) g(z)` for
`avgμ c ⊗ volume`. The `z`-region is `cell ∩ {|η| ≤ L}` (bounded, `g` bounded there), `y` ranges
over the support ball of `ρ`, and `∫∫ |ρ(y)| |D_i(z-y)| ≤ ‖ρ‖_∞ ‖g‖_∞ ∫_{box} |D_i|` with `D`
locally integrable (`CylLocInt`). -/
def CylSwapInt1 : Prop :=
  ∀ c r : ℝ, 0 < c → 1 < r → ∀ D : ℝ × ℝ → CMerid, CylLp c r D →
    ∀ (ρ : ContDiffBump (0 : ℝ × ℝ)) (g : ℝ × ℝ → ℝ), SwapGood c g → ∀ i : Fin 2,
      Integrable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
        ((ρ.normed volume p.2 : ℝ) : ℂ) * D (p.1 - p.2) i * ((g p.1 : ℝ) : ℂ))
        ((UnforcedLeray.Cyl.avgμ c).prod volume)

/-- **Leaf `T12/1/3/1/5/3/2`** (SP 1923-1926): integrability of `D_i(u) ρ(y) g(u+y)` for
`avgμ c ⊗ volume` (`u` in the cell, `|u_η| ≤ L + rOut`, `y` in the support ball of `ρ`). -/
def CylSwapInt2 : Prop :=
  ∀ c r : ℝ, 0 < c → 1 < r → ∀ D : ℝ × ℝ → CMerid, CylLp c r D →
    ∀ (ρ : ContDiffBump (0 : ℝ × ℝ)) (g : ℝ × ℝ → ℝ), SwapGood c g → ∀ i : Fin 2,
      Integrable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
        D p.1 i * ((ρ.normed volume p.2 * g (p.1 + p.2) : ℝ) : ℂ))
        ((UnforcedLeray.Cyl.avgμ c).prod volume)

/-- **Leaf `T12/1/3/1/5/3/3`** (SP 1923-1926): componentwise form of `cylMoll`,
`(∫ ρ(y) • D(z-y)) i = ∫ ρ(y) D_i(z-y)`; `y ↦ ρ(y) • D(z-y)` is integrable
(`HasCompactSupport.convolutionExists_left`, `D` locally integrable), then
`ContinuousLinearMap.integral_comp_comm` with the coordinate functional. -/
def CylMollComp : Prop :=
  ∀ c r : ℝ, 0 < c → 1 < r → ∀ D : ℝ × ℝ → CMerid, CylLp c r D →
    ∀ (ρ : ContDiffBump (0 : ℝ × ℝ)) (z : ℝ × ℝ) (i : Fin 2),
      cylMoll ρ D z i = ∫ y, ((ρ.normed volume y : ℝ) : ℂ) * D (z - y) i

theorem swapGood_fderiv {c : ℝ} {φ : ℝ × ℝ → ℝ} (hφ : CylTest c φ) (v : ℝ × ℝ) :
    SwapGood c (fun z => fderiv ℝ φ z v) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (hφ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  · intro w
    exact congrArg (fun L => L v) (Swap.fderiv_periodic_of hφ w)
  · obtain ⟨L, hL⟩ := Swap.fderiv_zero_of_far hφ
    exact ⟨L, fun z hz => by simp [hL z hz]⟩

theorem cylMollSwapDiv_of (h1 : CylSwapInt1) (h2 : CylSwapInt2) (h3 : CylMollComp) :
    CylMollSwapDiv := by
  intro c r hc hr D hD ρ φ hφ
  haveI : SFinite (UnforcedLeray.Cyl.avgμ c) := by
    unfold UnforcedLeray.Cyl.avgμ UnforcedLeray.Cyl.cellμ
    infer_instance
  set g0 : ℝ × ℝ → ℝ := fun z => fderiv ℝ φ z (1, 0) with hg0
  set g1 : ℝ × ℝ → ℝ := fun z => fderiv ℝ φ z (0, 1) with hg1
  have G0 : SwapGood c g0 := swapGood_fderiv hφ (1, 0)
  have G1 : SwapGood c g1 := swapGood_fderiv hφ (0, 1)
  have hper : UnforcedLeray.Cyl.IsPeriodic c D := hD.1
  -- integrability of the `z`-integrands
  have L0 : Integrable (fun z => (∫ y, ((ρ.normed volume y : ℝ) : ℂ) * D (z - y) 0) * ((g0 z : ℝ) : ℂ))
      (UnforcedLeray.Cyl.avgμ c) := by
    have := (h1 c r hc hr D hD ρ g0 G0 0).integral_prod_left
    refine this.congr (Eventually.of_forall fun z => ?_)
    dsimp only
    exact integral_mul_const _ _
  have L1 : Integrable (fun z => (∫ y, ((ρ.normed volume y : ℝ) : ℂ) * D (z - y) 1) * ((g1 z : ℝ) : ℂ))
      (UnforcedLeray.Cyl.avgμ c) := by
    have := (h1 c r hc hr D hD ρ g1 G1 1).integral_prod_left
    refine this.congr (Eventually.of_forall fun z => ?_)
    dsimp only
    exact integral_mul_const _ _
  have R0 : Integrable (fun u => D u 0 * ((∫ y, ρ.normed volume y * g0 (u + y) : ℝ) : ℂ))
      (UnforcedLeray.Cyl.avgμ c) := by
    have := (h2 c r hc hr D hD ρ g0 G0 0).integral_prod_left
    refine this.congr (Eventually.of_forall fun u => ?_)
    dsimp only
    have h : ((∫ y, ρ.normed volume y * g0 (u + y) : ℝ) : ℂ)
        = ∫ y, ((ρ.normed volume y * g0 (u + y) : ℝ) : ℂ) := integral_ofReal.symm
    rw [h, ← integral_const_mul]
  have R1 : Integrable (fun u => D u 1 * ((∫ y, ρ.normed volume y * g1 (u + y) : ℝ) : ℂ))
      (UnforcedLeray.Cyl.avgμ c) := by
    have := (h2 c r hc hr D hD ρ g1 G1 1).integral_prod_left
    refine this.congr (Eventually.of_forall fun u => ?_)
    dsimp only
    have h : ((∫ y, ρ.normed volume y * g1 (u + y) : ℝ) : ℂ)
        = ∫ y, ((ρ.normed volume y * g1 (u + y) : ℝ) : ℂ) := integral_ofReal.symm
    rw [h, ← integral_const_mul]
  have e0 := Swap.swap_component hc D hper 0 ρ g0 G0.2.1 (h1 c r hc hr D hD ρ g0 G0 0)
    (h2 c r hc hr D hD ρ g0 G0 0)
  have e1 := Swap.swap_component hc D hper 1 ρ g1 G1.2.1 (h1 c r hc hr D hD ρ g1 G1 1)
    (h2 c r hc hr D hD ρ g1 G1 1)
  have hL : (fun z => cylMoll ρ D z 0 * ((fderiv ℝ φ z (1, 0) : ℝ) : ℂ)
        + cylMoll ρ D z 1 * ((fderiv ℝ φ z (0, 1) : ℝ) : ℂ))
      = fun z => (∫ y, ((ρ.normed volume y : ℝ) : ℂ) * D (z - y) 0) * ((g0 z : ℝ) : ℂ)
        + (∫ y, ((ρ.normed volume y : ℝ) : ℂ) * D (z - y) 1) * ((g1 z : ℝ) : ℂ) := by
    funext z
    rw [h3 c r hc hr D hD ρ z 0, h3 c r hc hr D hD ρ z 1]
  rw [hL, integral_add L0 L1, integral_add R0 R1, e0, e1]

end UnforcedLeray.Short.IIb

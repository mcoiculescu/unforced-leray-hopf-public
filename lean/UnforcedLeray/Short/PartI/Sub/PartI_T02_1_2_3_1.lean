import UnforcedLeray.Short.PartI.Sub.T02_1_2

/-!
# Part I, task `PartI:T02/1/2/3/1`: cylinder Leibniz rule for `scalarH3Mul` (conditional)

Source of record: `the November 2 reference manuscript`, lines 261-288.

Target `bdp_scalar_leibniz`: if `x, y ∈ H³(C_c)` have weak `∂_j`-derivatives `x', y' ∈ H³`, then
`scalarH3Mul x y` has the weak `∂_j`-derivative `scalarH3Mul x' y + scalarH3Mul x y'`
(periodic weak derivatives on the cylinder).

The classical Leibniz rule for smooth periodic functions is proved here
(`bdp_smooth_leibniz`).  Two analytic leaves remain:

* `BdpWeakClosed`: the periodic weak derivative relation is closed under `L²`-convergence of
  functions and of derivatives (tests are bounded with compact support, the cell has finite
  measure in the periodic direction);
* `BdpSmoothApprox`: smooth periodic approximants `f_n → x`, `g_n → y` in `H³` (library:
  `TrainB.exists_smoothH3_sequence`, `exists_smooth_h3_product_limit`) with
  `f_n g_n → xy` and `∂_j f_n g_n + f_n ∂_j g_n → x'y + xy'` in `L²` of the cell; uses
  `H³ ⊂ L^∞` (`exists_scalarH3_bcf_representative`), `∂_j f_n → ∂_j x = x'` in `L²`
  (`Short/PartI/Sub/T02_1_2_2/WeakDerivCell.lean`, `weakDerivCell_proof`).

`bdp_scalar_leibniz_of` proves the target from the two leaves.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.TrainB
open UnforcedLeray.HeatCylinder

/-- **Leaf (closedness)**: if `fs n` has weak `∂_j`-derivative `fs' n` on the cylinder and
`fs n → F`, `fs' n → F'` in `L²` of the cell, then `F'` is the weak `∂_j`-derivative of `F`. -/
def BdpWeakClosed : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (j : Fin 2) (F F' : Plane → ℝ) (fs fs' : ℕ → Plane → ℝ),
    (∀ n, Sob.HasWeakDeriv (Sob.cylinder c) [(Sob.cylinder c).dir j] (fs n) (fs' n)) →
    MemLp F 2 (Sob.cylinder c).μ → MemLp F' 2 (Sob.cylinder c).μ →
    Tendsto (fun n => eLpNorm (fs n - F) 2 (Sob.cylinder c).μ) atTop (nhds 0) →
    Tendsto (fun n => eLpNorm (fs' n - F') 2 (Sob.cylinder c).μ) atTop (nhds 0) →
    Sob.HasWeakDeriv (Sob.cylinder c) [(Sob.cylinder c).dir j] F F'

/-- **Leaf (approximation)**: smooth periodic approximants of the pair `(x, y)` along which both
the products and the Leibniz right-hand sides converge in `L²` of the cell. -/
def BdpSmoothApprox : Prop :=
  ∀ (c : ℝ), 1 ≤ c → ∀ (j : Fin 2) (x x' y y' : ScalarH3 c),
    Sob.HasWeakDeriv (Sob.cylinder c) [(Sob.cylinder c).dir j]
      (Cyl.H.val x : Plane → ℝ) (Cyl.H.val x' : Plane → ℝ) →
    Sob.HasWeakDeriv (Sob.cylinder c) [(Sob.cylinder c).dir j]
      (Cyl.H.val y : Plane → ℝ) (Cyl.H.val y' : Plane → ℝ) →
    ∃ f g : ℕ → Plane → ℝ, (∀ n, Sob.IsCylSmooth c (f n)) ∧ (∀ n, Sob.IsCylSmooth c (g n)) ∧
      Tendsto (fun n => eLpNorm ((fun z => f n z * g n z) -
        fun z => (Cyl.H.val x : Plane → ℝ) z * (Cyl.H.val y : Plane → ℝ) z)
          2 (Sob.cylinder c).μ) atTop (nhds 0) ∧
      Tendsto (fun n => eLpNorm ((fun z =>
          fderiv ℝ (f n) z ((Sob.cylinder c).dir j) * g n z +
            f n z * fderiv ℝ (g n) z ((Sob.cylinder c).dir j)) -
        fun z => (Cyl.H.val x' : Plane → ℝ) z * (Cyl.H.val y : Plane → ℝ) z +
          (Cyl.H.val x : Plane → ℝ) z * (Cyl.H.val y' : Plane → ℝ) z)
          2 (Sob.cylinder c).μ) atTop (nhds 0)

theorem bdp_memLp_value {c : ℝ} (z : ScalarH3 c) :
    MemLp (Cyl.H.val z : Plane → ℝ) 2 (Sob.cylinder c).μ := by
  have e : Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ)) = (Sob.cylinder c).μ := by
    rw [Cyl.wμ_ρwW]; simp [Cyl.wμ]; exact (Cyl.cylinder_μ_eq c).symm
  have key : ∀ g : Plane → ℝ, MemLp g 2 (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))) →
      MemLp g 2 (Sob.cylinder c).μ := fun g hg => by rw [e] at hg; exact hg
  exact key _ (Lp.memLp (Sob.W.value (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2 z))

theorem bdp_ae_cell {c : ℝ} {a b : Plane → ℝ} (h : a =ᵐ[Cyl.cellμ c] b) :
    a =ᵐ[(Sob.cylinder c).μ] b := by
  rwa [Cyl.cylinder_μ_eq]

/-- Classical Leibniz rule for smooth periodic functions, in weak form. -/
theorem bdp_smooth_leibniz {c : ℝ} (hc : 0 < c) (j : Fin 2) {f g : Plane → ℝ}
    (hf : Sob.IsCylSmooth c f) (hg : Sob.IsCylSmooth c g) :
    Sob.HasWeakDeriv (Sob.cylinder c) [(Sob.cylinder c).dir j] (fun z => f z * g z)
      (fun z => fderiv ℝ f z ((Sob.cylinder c).dir j) * g z +
        f z * fderiv ℝ g z ((Sob.cylinder c).dir j)) := by
  have hfg : Sob.IsCylSmooth c (fun z => f z * g z) := TrainB.IsCylSmooth.mul hf hg
  have h := Sob.hasWeakDeriv_cylinder_of_isCylSmooth hc hfg [(Sob.cylinder c).dir j]
  convert h using 1
  funext z
  simp only [Sob.iterD_cons, Sob.iterD_nil]
  have := ((hf.smooth.differentiable (by simp) z).hasFDerivAt.mul
    (hg.smooth.differentiable (by simp) z).hasFDerivAt).fderiv
  change _ = (fderiv ℝ (f * g) z) _
  rw [this]
  simp [mul_comm, add_comm]

theorem bdp_scalar_leibniz_of (hC : BdpWeakClosed) (hA : BdpSmoothApprox) {c : ℝ} (hc1 : 1 ≤ c)
    (j : Fin 2) (x x' y y' : ScalarH3 c) :
    Sob.HasWeakDeriv (Sob.cylinder c) [(Sob.cylinder c).dir j]
      (Cyl.H.val x : Plane → ℝ) (Cyl.H.val x' : Plane → ℝ) →
    Sob.HasWeakDeriv (Sob.cylinder c) [(Sob.cylinder c).dir j]
      (Cyl.H.val y : Plane → ℝ) (Cyl.H.val y' : Plane → ℝ) →
    Sob.HasWeakDeriv (Sob.cylinder c) [(Sob.cylinder c).dir j]
      (Cyl.H.val (scalarH3Mul hc1 x y) : Plane → ℝ)
      (Cyl.H.val (scalarH3Mul hc1 x' y + scalarH3Mul hc1 x y') : Plane → ℝ) := by
  intro hx hy
  have hc : 0 < c := by linarith
  obtain ⟨f, g, hf, hg, t1, t2⟩ := hA c hc1 j x x' y y' hx hy
  have hF : (fun z => (Cyl.H.val x : Plane → ℝ) z * (Cyl.H.val y : Plane → ℝ) z)
      =ᵐ[(Sob.cylinder c).μ] (Cyl.H.val (scalarH3Mul hc1 x y) : Plane → ℝ) :=
    (bdp_ae_cell (scalarH3Mul_value_ae hc1 x y)).symm
  have hF' : (fun z => (Cyl.H.val x' : Plane → ℝ) z * (Cyl.H.val y : Plane → ℝ) z +
      (Cyl.H.val x : Plane → ℝ) z * (Cyl.H.val y' : Plane → ℝ) z)
      =ᵐ[(Sob.cylinder c).μ]
        (Cyl.H.val (scalarH3Mul hc1 x' y + scalarH3Mul hc1 x y') : Plane → ℝ) := by
    have h1 := bdp_ae_cell (scalarH3Mul_value_ae hc1 x' y)
    have h2 := bdp_ae_cell (scalarH3Mul_value_ae hc1 x y')
    have h3 := bdp_ae_cell (scalarH3_value_add_ae (scalarH3Mul hc1 x' y) (scalarH3Mul hc1 x y'))
    filter_upwards [h1, h2, h3] with z e1 e2 e3
    rw [e3, e1, e2]
  have hmF : MemLp (fun z => (Cyl.H.val x : Plane → ℝ) z * (Cyl.H.val y : Plane → ℝ) z) 2
      (Sob.cylinder c).μ := (bdp_memLp_value _).ae_eq hF.symm
  have hmF' : MemLp (fun z => (Cyl.H.val x' : Plane → ℝ) z * (Cyl.H.val y : Plane → ℝ) z +
      (Cyl.H.val x : Plane → ℝ) z * (Cyl.H.val y' : Plane → ℝ) z) 2 (Sob.cylinder c).μ :=
    (bdp_memLp_value _).ae_eq hF'.symm
  have key := hC c hc j _ _ (fun n z => f n z * g n z)
    (fun n z => fderiv ℝ (f n) z ((Sob.cylinder c).dir j) * g n z +
      f n z * fderiv ℝ (g n) z ((Sob.cylinder c).dir j))
    (fun n => bdp_smooth_leibniz hc j (hf n) (hg n)) hmF hmF' t1 t2
  exact key.congr_ae hF hF'

end UnforcedLeray.Short.PartI

#print axioms UnforcedLeray.Short.PartI.bdp_scalar_leibniz_of

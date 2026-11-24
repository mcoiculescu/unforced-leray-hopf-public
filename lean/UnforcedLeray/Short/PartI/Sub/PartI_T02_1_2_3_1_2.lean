import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_2_3_1

/-!
# Part I, task `PartI:T02/1/2/3/1/2`: smooth approximation for the cylinder Leibniz rule

Source of record: `the November 2 reference manuscript`, lines 261-288.

`bdp_smoothApprox_of` proves `BdpSmoothApprox` from two leaves:
* `BdpProdConv`: `L²` convergence of products when one factor is bounded;
* `BdpSmoothSeq`: smooth periodic approximants of `x, y` with `L²` convergence of the functions
  and of their `j`-th derivatives, uniformly bounded (`H³ ⊂ L^∞`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.TrainB
open UnforcedLeray.HeatCylinder

/-- **Leaf (products)**: (source lines 261-288, the `(f_n - x) g_n + x (g_n - y)` splitting)
if `u` is a.e. bounded by `M`, every `vs n` is a.e. bounded by `M`, `us n → u` and `vs n → v` in
`L²` of the cylinder, then `us n * vs n → u * v` in `L²`. -/
def BdpProdConv : Prop :=
  ∀ (c : ℝ) (M : ℝ) (u v : Plane → ℝ) (us vs : ℕ → Plane → ℝ),
    AEStronglyMeasurable u (Sob.cylinder c).μ → AEStronglyMeasurable v (Sob.cylinder c).μ →
    (∀ n, AEStronglyMeasurable (us n) (Sob.cylinder c).μ) →
    (∀ n, AEStronglyMeasurable (vs n) (Sob.cylinder c).μ) →
    (∀ᵐ z ∂(Sob.cylinder c).μ, |u z| ≤ M) →
    (∀ n, ∀ᵐ z ∂(Sob.cylinder c).μ, |vs n z| ≤ M) →
    Tendsto (fun n => eLpNorm (us n - u) 2 (Sob.cylinder c).μ) atTop (nhds 0) →
    Tendsto (fun n => eLpNorm (vs n - v) 2 (Sob.cylinder c).μ) atTop (nhds 0) →
    Tendsto (fun n => eLpNorm ((fun z => us n z * vs n z) - fun z => u z * v z) 2
      (Sob.cylinder c).μ) atTop (nhds 0)

/-- **Leaf (smooth sequences)**: (source lines 261-288) for `x, y ∈ H³(C_c)` with weak
`∂_j`-derivatives `x', y' ∈ H³`, there are smooth periodic `f n → x`, `g n → y` with
`∂_j f n → x'`, `∂_j g n → y'` in `L²` of the cylinder, and a common bound `M` for
`x, y, x', y'` (`H³ ⊂ L^∞`, `exists_scalarH3_bcf_representative`) and for every `f n`, `g n`
(sup norm controlled by the `H³` norm). Uses `TrainB.exists_smoothH3_sequence`, continuity of
`Sob.W.deriv`, and `weakDerivCell_proof`. -/
def BdpSmoothSeq : Prop :=
  ∀ (c : ℝ), 1 ≤ c → ∀ (j : Fin 2) (x x' y y' : ScalarH3 c),
    Sob.HasWeakDeriv (Sob.cylinder c) [(Sob.cylinder c).dir j]
      (Cyl.H.val x : Plane → ℝ) (Cyl.H.val x' : Plane → ℝ) →
    Sob.HasWeakDeriv (Sob.cylinder c) [(Sob.cylinder c).dir j]
      (Cyl.H.val y : Plane → ℝ) (Cyl.H.val y' : Plane → ℝ) →
    ∃ (f g : ℕ → Plane → ℝ) (M : ℝ), (∀ n, Sob.IsCylSmooth c (f n)) ∧
      (∀ n, Sob.IsCylSmooth c (g n)) ∧
      (∀ᵐ z ∂(Sob.cylinder c).μ, |(Cyl.H.val x : Plane → ℝ) z| ≤ M) ∧
      (∀ᵐ z ∂(Sob.cylinder c).μ, |(Cyl.H.val y : Plane → ℝ) z| ≤ M) ∧
      (∀ᵐ z ∂(Sob.cylinder c).μ, |(Cyl.H.val x' : Plane → ℝ) z| ≤ M) ∧
      (∀ᵐ z ∂(Sob.cylinder c).μ, |(Cyl.H.val y' : Plane → ℝ) z| ≤ M) ∧
      (∀ n, ∀ᵐ z ∂(Sob.cylinder c).μ, |f n z| ≤ M) ∧
      (∀ n, ∀ᵐ z ∂(Sob.cylinder c).μ, |g n z| ≤ M) ∧
      Tendsto (fun n => eLpNorm (f n - (Cyl.H.val x : Plane → ℝ)) 2 (Sob.cylinder c).μ)
        atTop (nhds 0) ∧
      Tendsto (fun n => eLpNorm (g n - (Cyl.H.val y : Plane → ℝ)) 2 (Sob.cylinder c).μ)
        atTop (nhds 0) ∧
      Tendsto (fun n => eLpNorm ((fun z => fderiv ℝ (f n) z ((Sob.cylinder c).dir j)) -
        (Cyl.H.val x' : Plane → ℝ)) 2 (Sob.cylinder c).μ) atTop (nhds 0) ∧
      Tendsto (fun n => eLpNorm ((fun z => fderiv ℝ (g n) z ((Sob.cylinder c).dir j)) -
        (Cyl.H.val y' : Plane → ℝ)) 2 (Sob.cylinder c).μ) atTop (nhds 0)

theorem bdp_smoothApprox_of (h1 : BdpProdConv) (h2 : BdpSmoothSeq) : BdpSmoothApprox := by
  intro c hc1 j x x' y y' hx hy
  obtain ⟨f, g, M, hf, hg, bx, by', bx', by'', bf, bg, tf, tg, tf', tg'⟩ :=
    h2 c hc1 j x x' y y' hx hy
  refine ⟨f, g, hf, hg, ?_, ?_⟩
  · exact h1 c M _ _ (fun n => f n) (fun n => g n)
      (bdp_memLp_value x).aestronglyMeasurable (bdp_memLp_value y).aestronglyMeasurable
      (fun n => (hf n).smooth.continuous.aestronglyMeasurable)
      (fun n => (hg n).smooth.continuous.aestronglyMeasurable) bx bg tf tg
  · have mdf : ∀ n, AEStronglyMeasurable (fun z => fderiv ℝ (f n) z ((Sob.cylinder c).dir j))
        (Sob.cylinder c).μ := fun n =>
      (((hf n).smooth.continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable
    have mdg : ∀ n, AEStronglyMeasurable (fun z => fderiv ℝ (g n) z ((Sob.cylinder c).dir j))
        (Sob.cylinder c).μ := fun n =>
      (((hg n).smooth.continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable
    have mf : ∀ n, AEStronglyMeasurable (f n) (Sob.cylinder c).μ := fun n =>
      (hf n).smooth.continuous.aestronglyMeasurable
    have mg : ∀ n, AEStronglyMeasurable (g n) (Sob.cylinder c).μ := fun n =>
      (hg n).smooth.continuous.aestronglyMeasurable
    have mx := (bdp_memLp_value x).aestronglyMeasurable
    have my := (bdp_memLp_value y).aestronglyMeasurable
    have mx' := (bdp_memLp_value x').aestronglyMeasurable
    have my' := (bdp_memLp_value y').aestronglyMeasurable
    have T1 := h1 c M _ _ _ _ mx' my mdf mg bx' bg tf' tg
    have T2 := h1 c M _ _ _ _ my' mx mdg mf by'' bf tg' tf
    have hm1 : ∀ n, AEStronglyMeasurable ((fun z => fderiv ℝ (f n) z ((Sob.cylinder c).dir j) * g n z) -
        fun z => (Cyl.H.val x' : Plane → ℝ) z * (Cyl.H.val y : Plane → ℝ) z) (Sob.cylinder c).μ :=
      fun n => (mdf n).mul (mg n) |>.sub (mx'.mul my)
    have hm2 : ∀ n, AEStronglyMeasurable ((fun z => fderiv ℝ (g n) z ((Sob.cylinder c).dir j) * f n z) -
        fun z => (Cyl.H.val y' : Plane → ℝ) z * (Cyl.H.val x : Plane → ℝ) z) (Sob.cylinder c).μ :=
      fun n => (mdg n).mul (mf n) |>.sub (my'.mul mx)
    have hsum := T1.add T2
    rw [add_zero] at hsum
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun n => zero_le)
      (fun n => ?_)
    refine le_trans (le_of_eq ?_) (eLpNorm_add_le (hm1 n) (hm2 n) (by norm_num))
    congr 1
    funext z
    simp only [Pi.sub_apply, Pi.add_apply]
    ring

end UnforcedLeray.Short.PartI

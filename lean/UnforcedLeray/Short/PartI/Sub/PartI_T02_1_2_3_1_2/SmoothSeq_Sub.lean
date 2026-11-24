import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_2_3_1_2

/-!
# Decomposition of `bdp_smoothSeq` (task `PartI:T02/1/2/3/1/2/2`)

Source: `the November 2 reference manuscript`,
lines 261-288.  Three leaves, then the assembly `bdp_smoothSeq_of`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.TrainB

/-- **Leaf 1** (source 261-288, `H³ ⊂ L^∞` and density of smooth functions): every `x ∈ H³(C_c)`
is the `H³`-limit of smooth periodic `f n`, with `f n → x` in `L²` of the cylinder and a common
a.e. bound `M` for `x` and all `f n` (use `exists_h3_uniform_representative_sequence`: the
`f n` converge uniformly, so are uniformly bounded; identify `cellμ c` with `(cylinder c).μ`
a.e.; `L²` convergence from `Sob.W.value` continuity and `W.value_ofCylSmooth`). -/
def BdpSmoothFun : Prop :=
  ∀ (c : ℝ) (hc : 1 ≤ c) (x : ScalarH3 c),
    ∃ (f : ℕ → Plane → ℝ) (hf : ∀ n, Sob.IsCylSmooth c (f n)) (M : ℝ),
      Tendsto (fun n => Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (k := 3) (p := 2)
        (by linarith) (f n) (hf n)) atTop (nhds x) ∧
      (∀ᵐ z ∂(Sob.cylinder c).μ, |(Cyl.H.val x : Plane → ℝ) z| ≤ M) ∧
      (∀ n, ∀ᵐ z ∂(Sob.cylinder c).μ, |f n z| ≤ M) ∧
      Tendsto (fun n => eLpNorm (f n - (Cyl.H.val x : Plane → ℝ)) 2 (Sob.cylinder c).μ)
        atTop (nhds 0)

/-- **Leaf 2** (`H³ ⊂ L^∞`, `exists_scalarH3_bcf_representative`): every `H³` class has an
a.e. bounded value on the cylinder. -/
def BdpValueBound : Prop :=
  ∀ (c : ℝ), 1 ≤ c → ∀ z : ScalarH3 c,
    ∃ M : ℝ, ∀ᵐ w ∂(Sob.cylinder c).μ, |(Cyl.H.val z : Plane → ℝ) w| ≤ M

/-- **Leaf 3** (source 261-288, continuity of `Sob.W.deriv`, `W.deriv_ofCylSmooth`,
`HasWeakDeriv.ae_unique` as in `weakDerivCell_proof`): if smooth `f n` converge to `x` in `H³`
and `x` has weak `∂_j`-derivative `x'`, then the classical derivatives `∂_j f n → x'` in `L²`. -/
def BdpDerivConv : Prop :=
  ∀ (c : ℝ) (hc : 1 ≤ c) (j : Fin 2) (x x' : ScalarH3 c),
    Sob.HasWeakDeriv (Sob.cylinder c) [(Sob.cylinder c).dir j]
      (Cyl.H.val x : Plane → ℝ) (Cyl.H.val x' : Plane → ℝ) →
    ∀ (f : ℕ → Plane → ℝ) (hf : ∀ n, Sob.IsCylSmooth c (f n)),
      Tendsto (fun n => Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (k := 3) (p := 2)
        (by linarith) (f n) (hf n)) atTop (nhds x) →
      Tendsto (fun n => eLpNorm ((fun z => fderiv ℝ (f n) z ((Sob.cylinder c).dir j)) -
        (Cyl.H.val x' : Plane → ℝ)) 2 (Sob.cylinder c).μ) atTop (nhds 0)

private lemma ae_bound_mono {μ : Measure Plane} {u : Plane → ℝ} {M M' : ℝ}
    (h : ∀ᵐ z ∂μ, |u z| ≤ M) (hM : M ≤ M') : ∀ᵐ z ∂μ, |u z| ≤ M' :=
  h.mono fun _ hz => hz.trans hM

theorem bdp_smoothSeq_of (h1 : BdpSmoothFun) (h2 : BdpValueBound) (h3 : BdpDerivConv) :
    BdpSmoothSeq := by
  intro c hc j x x' y y' hx hy
  obtain ⟨f, hf, Mx, hfx, bx, bf, tf⟩ := h1 c hc x
  obtain ⟨g, hg, My, hgy, by1, bg, tg⟩ := h1 c hc y
  obtain ⟨Mx', bx'⟩ := h2 c hc x'
  obtain ⟨My', by'⟩ := h2 c hc y'
  have tf' := h3 c hc j x x' hx f hf hfx
  have tg' := h3 c hc j y y' hy g hg hgy
  set M := max (max Mx My) (max Mx' My') with hM
  have h1' : Mx ≤ M := (le_max_left _ _).trans (le_max_left _ _)
  have h2' : My ≤ M := (le_max_right _ _).trans (le_max_left _ _)
  have h3' : Mx' ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have h4' : My' ≤ M := (le_max_right _ _).trans (le_max_right _ _)
  exact ⟨f, g, M, hf, hg, ae_bound_mono bx h1', ae_bound_mono by1 h2', ae_bound_mono bx' h3',
    ae_bound_mono by' h4', fun n => ae_bound_mono (bf n) h1', fun n => ae_bound_mono (bg n) h2',
    tf, tg, tf', tg'⟩

end UnforcedLeray.Short.PartI

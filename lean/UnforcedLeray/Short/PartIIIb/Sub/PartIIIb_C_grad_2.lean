import UnforcedLeray.Short.PartIIIb.Concrete.AffineGradPin
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.PsipADiff

/-!
# `PartIII-b:C/grad/2`: `HhatADiff` reduced to six lattice-sum differentiability leaves

Source `the November 2 reference manuscript` lines 4978-4980 (`ĥ_A =
√s[(h^p_A)_r e_r + ((h^p_A)_z + ε(1-𝒦)ψ^p_A)e_z]`, "the sums and their required derivatives
converge by Gaussian decay"), 4741-4745 (`A` is `C^6`), 5081-5084 (derivative budget).
`𝒦ψ = η∂_ηψ + 2s∂_sψ`, so `ĥ_A` is differentiable in `x` and in `s` as soon as `h^p_A`,
`ψ^p_A` are, and `∂_ηψ^p_A`, `∂_sψ^p_A` are again differentiable in `x` and in `s`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Leaf 1 (source 4973, 4978): `x ↦ h^p_A(s, x)` is differentiable. -/
def HpADiffX (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  ∀ (ν : ℝ), 0 < ν → ∀ (A : ℝ → Mat3), IsAffElem as A → ∀ s : ℝ, 0 < s → ∀ x : ℝ × ℝ,
    DifferentiableAt ℝ (hpA ν χf A s) x

/-- Leaf 2 (source 4973, 4978, 4741-4745): `s' ↦ h^p_A(s', x)` is differentiable at `s > 0`. -/
def HpADiffS (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  ∀ (ν : ℝ), 0 < ν → ∀ (A : ℝ → Mat3), IsAffElem as A → ∀ s : ℝ, 0 < s → ∀ x : ℝ × ℝ,
    DifferentiableAt ℝ (fun s' => hpA ν χf A s' x) s

/-- Leaf 3 (source 4974-4980): `y ↦ ∂_η ψ^p_A(s, y)` is differentiable (second `x`-derivative). -/
def PsipAXSecond (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  ∀ (ν : ℝ), 0 < ν → ∀ (A : ℝ → Mat3), IsAffElem as A → ∀ s : ℝ, 0 < s → ∀ x : ℝ × ℝ,
    DifferentiableAt ℝ (fun y => fderiv ℝ (psipA ν χf A s) y (ei 1)) x

/-- Leaf 4 (source 4974-4980): `y ↦ ∂_s ψ^p_A(s, y)` is differentiable in `y`
(mixed derivative `∂_x∂_s`). -/
def PsipAMixedX (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  ∀ (ν : ℝ), 0 < ν → ∀ (A : ℝ → Mat3), IsAffElem as A → ∀ s : ℝ, 0 < s → ∀ x : ℝ × ℝ,
    DifferentiableAt ℝ (fun y => deriv (fun s' => psipA ν χf A s' y) s) x

/-- Leaf 5 (source 4974-4980): `s' ↦ ∂_η ψ^p_A(s', x)` is differentiable at `s > 0`
(mixed derivative `∂_s∂_x`). -/
def PsipAMixedS (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  ∀ (ν : ℝ), 0 < ν → ∀ (A : ℝ → Mat3), IsAffElem as A → ∀ s : ℝ, 0 < s → ∀ x : ℝ × ℝ,
    DifferentiableAt ℝ (fun s' => fderiv ℝ (psipA ν χf A s') x (ei 1)) s

/-- Leaf 6 (source 4974-4980, 4741-4745): `s' ↦ ∂_s ψ^p_A(s', x)` is differentiable at `s > 0`
(second `s`-derivative). -/
def PsipASSecond (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  ∀ (ν : ℝ), 0 < ν → ∀ (A : ℝ → Mat3), IsAffElem as A → ∀ s : ℝ, 0 < s → ∀ x : ℝ × ℝ,
    DifferentiableAt ℝ (fun s' => deriv (fun s'' => psipA ν χf A s'' x) s') s

theorem hhatADiff_of (as : ℝ) (χf : ℝ → ℝ) (hχ : IsSourceCutoffC χf)
    (h1 : HpADiffX as χf) (h2 : HpADiffS as χf) (h3 : PsipAXSecond as χf)
    (h4 : PsipAMixedX as χf) (h5 : PsipAMixedS as χf) (h6 : PsipASSecond as χf) :
    HhatADiff as χf := by
  intro ν ε hν A hA s hs x i
  have hpsi := psipADiff as χf hχ ν hν A hA s hs x
  have a1 := h1 ν hν A hA s hs x
  have a2 := h2 ν hν A hA s hs x
  have a3 := h3 ν hν A hA s hs x
  have a4 := h4 ν hν A hA s hs x
  have a5 := h5 ν hν A hA s hs x
  have a6 := h6 ν hν A hA s hs x
  -- the 𝒦-term, in x and in s
  have Kx : DifferentiableAt ℝ (fun y => Kop (fun s' z => psipA ν χf A s' z) s y) x := by
    unfold Kop
    exact (differentiableAt_snd.mul a3).add (a4.const_mul _)
  have Ks : DifferentiableAt ℝ (fun s' => Kop (fun s'' z => psipA ν χf A s'' z) s' x) s := by
    unfold Kop
    exact (a5.const_mul _).add ((differentiableAt_id.const_mul 2).mul a6)
  have sx : DifferentiableAt ℝ (fun _ : ℝ × ℝ => Real.sqrt s) x := differentiableAt_const _
  have ss : DifferentiableAt ℝ (fun s' : ℝ => Real.sqrt s') s := (Real.hasDerivAt_sqrt hs.ne').differentiableAt
  fin_cases i
  · constructor
    · show DifferentiableAt ℝ (fun y => Real.sqrt s * (hpA ν χf A s y).1) x
      exact DifferentiableAt.mul (differentiableAt_const _) a1.fst
    · show DifferentiableAt ℝ (fun s' => Real.sqrt s' * (hpA ν χf A s' x).1) s
      exact DifferentiableAt.mul ss a2.fst
  · simp [chartComp_hhatA_phi]
  · constructor
    · show DifferentiableAt ℝ (fun y => Real.sqrt s * ((hpA ν χf A s y).2 + ε *
        (psipA ν χf A s y - Kop (fun s' z => psipA ν χf A s' z) s y))) x
      exact DifferentiableAt.mul (differentiableAt_const _)
        (a1.snd.add ((hpsi.1.sub Kx).const_mul ε))
    · show DifferentiableAt ℝ (fun s' => Real.sqrt s' * ((hpA ν χf A s' x).2 + ε *
        (psipA ν χf A s' x - Kop (fun s'' z => psipA ν χf A s'' z) s' x))) s
      exact DifferentiableAt.mul ss (a2.snd.add ((hpsi.2.sub Ks).const_mul ε))

end UnforcedLeray.Short.PartIIIb.Concrete

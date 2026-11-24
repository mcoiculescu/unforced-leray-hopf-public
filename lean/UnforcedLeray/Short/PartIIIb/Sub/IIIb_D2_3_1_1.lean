import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.Defs
import UnforcedLeray.Short.PartIIIa.SeparatedKernels

/-!
# Decomposition of `wardX0Smooth_of` (`PartIII-b:IIIb-D2/3/1/1`)

Source of record: `the November 2 reference manuscript` 3604-3621 (`sep:kernel`,
`sep:resolvent`), 3631-3646 (`sep:young`), 4155-4160, 4171, 2684-2703.

`X₀ = W_μ - W_{μ+1}` is `C²` in `y` on the young region.  The proof splits into

* `OldSourceReg`: the old physical source `oldPhys R c (g₁+g₂)` of a `StrG` element is, up to a
  null set of `(τ,z)` (which does not change `sepW`), a measurable `P`-periodic tensor supported
  in `|z'| ≤ R√(5ν/6)` with finite `L²_τL²_z` moment (4155-4156: `T ∈ Y₂`, by the lift identity
  2684-2687 and `W ≥ 1`; `chiOStr` vanishes for `s ≤ 1.2/ν`);
* `SepWSmoothOn`: for such a source `W_μ(·,τ)` is `C²` on `{|y'| > r_o}` (`sep:resolvent` plus
  `sep:kernel`: `|D^j∇K_t(x)| ≤ C|x|^{-4-j}`, `|y-λz| ≥ |y'|-λ|z'|` on the young region,
  differentiation under both integrals).

**Moment class.** The finer `N₁` / `L²_τL^{22/19}` moments of 4156-4158 are properties of the
actual stresses `T = M_Uw` of the pair graph (the repair part by the repair-product bounds); an
arbitrary `T ∈ Z` has no transverse decay in its repair component, so its old source need not be
in `L²_τL^{22/19}`.  The Ward Props are stated for every `T ∈ StrG`, hence the moment used here is
the one every `T ∈ Z` has: `Y₂ = L²_τL²` (`sep:young` with `p = 2`: `2Re μ + 3/2 > 0`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Finite `L²_τ L²_z` (`Y₂`) moment of a separated source (source 4155-4156: `T ∈ Y₂`; the lift
identity `‖𝒩_TT‖²_{Y₂} = πR²‖T‖²_{H_T}`, 2684-2687; `sep:young` with `p = 2`, 3631-3646). -/
def SepMoment (P : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  IIIa.ltauLq P 2 (IIIa.srcNorm T) < ⊤

/-- **`sep:resolvent` + `sep:kernel`** (3604-3621): `W_μ(·,τ)` is `C²` off the source disk, for a
`P`-periodic measurable source supported in `|z'| ≤ r_o` with finite `L²_τL²` moment. -/
def SepWSmoothOn : Prop :=
  ∀ (ν : ℝ) (μ : ℂ) (rOut P : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ),
    0 < ν → -(1 / 4) < μ.re → 0 ≤ rOut → 0 < P → IIIa.IsSepSource P rOut T → SepMoment P T →
    ∀ (τ : ℝ) (i : Fin 3),
      ContDiffOn ℝ 2 (fun y => IIIa.sepW ν μ T y τ i) {y : Space | rOut < ϱ y}

/-- **Source regularisation** (4155-4160, 4171, 2684-2703): for `c, ρ_b > 0`, `m_Z ≥ 0`, the old
source of the Ward field is a.e. a separated source with finite `Y₂` moment; `sepW` does not see
the null set; the a.e. identity `oldPhys R c (g₁+g₂) = T'` (in `(τ,z)`) is part of the
statement (it transfers integrability of the `sepW` integrand).  (`c, ρ_b > 0`: otherwise the chart measures vanish and `g₁, g₂` are arbitrary;
`m_Z ≥ 0`: `W ≥ 1`, the source fixes `m_Z > 3/2`, 2693.) -/
def OldSourceReg (c mZ ρb γ ν : ℝ) (ε : ℝ) {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo) : Prop :=
  0 < c → 0 < ρb → 0 ≤ mZ → 0 < ν → 0 < ε →
  ∀ (T : StrG c mZ ρb γ ν) (g₁ g₂ : Chart → Ten3),
    ((chiOStr c mZ ρb γ ν hχo T).fst : Chart → Ten3) =ᵐ[gainZ1Measure c mZ γ ν] g₁ →
    ((chiOStr c mZ ρb γ ν hχo T).snd : Chart → Ten3) =ᵐ[gainHTMeasure c ρb γ ν] g₂ →
      ∃ (P : ℝ) (T' : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ), 0 < P ∧
        IIIa.IsSepSource P (ε⁻¹ * Real.sqrt (5 * ν / 6)) T' ∧ SepMoment P T' ∧
        (∀ (μ : ℂ) (y : Space) (τ : ℝ),
          IIIa.sepW ν μ (oldPhys ε⁻¹ c (g₁ + g₂)) y τ = IIIa.sepW ν μ T' y τ) ∧
        ∀ᵐ x : ℝ × Space ∂volume, oldPhys ε⁻¹ c (g₁ + g₂) x.1 x.2 = T' x.1 x.2

theorem wardX0Smooth_of (c mZ ρb γ ν ε μ : ℝ) {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo)
    (hreg : OldSourceReg c mZ ρb γ ν ε hχo) (hW : SepWSmoothOn) :
    WardX0Smooth c mZ ρb γ ν ε μ hχo := by
  intro hc hρ hm hν hε hμ T g₁ g₂ h1 h2 τ
  obtain ⟨P, T', hP, hS, hM, hEq, -⟩ := hreg hc hρ hm hν hε T g₁ g₂ h1 h2
  have hr : 0 ≤ ε⁻¹ * Real.sqrt (5 * ν / 6) := by positivity
  have hset : youngOpen ν ε⁻¹ = {y : Space | ε⁻¹ * Real.sqrt (5 * ν / 6) < ϱ y} := rfl
  have hA := hW ν (μ : ℂ) _ P T' hν (by simpa using hμ) hr hP hS hM τ
  have hB := hW ν ((μ : ℂ) + 1) _ P T' hν (by simp; linarith) hr hP hS hM τ
  rw [hset]
  unfold wardX0
  refine contDiffOn_piLp' 2 fun i => ?_
  have hd : ContDiffOn ℝ 2 (fun y => IIIa.sepW ν (μ : ℂ) T' y τ i -
      IIIa.sepW ν ((μ : ℂ) + 1) T' y τ i) {y : Space | ε⁻¹ * Real.sqrt (5 * ν / 6) < ϱ y} :=
    (hA i).sub (hB i)
  have := Complex.reCLM.contDiff.comp_contDiffOn hd
  refine this.congr fun y _ => ?_
  simp [hEq]

end UnforcedLeray.Short.PartIIIb.Concrete

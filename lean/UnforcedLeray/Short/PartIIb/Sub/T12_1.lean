import UnforcedLeray.Short.PartIIb.Sub.T12

/-!
# Part II-b, task `PartII-b:T12/1` (`CylinderHelmholtzLr`): the cylinder Helmholtz decomposition in
`L^r` (conditional assembly and sub-leaves)

Source of record: `the November 2 reference manuscript`: line 1670 ("`P_0` the
ordinary planar cylinder projection"), lines 1923-1926 (`P_0` inside the causal formula), lines
1933-1935 ("The cylinder heat estimate follows by applying the Euclidean estimate to a cutoff of
`N` repeated cells, dividing its `r`-th power by `N`, and letting `N → ∞`. There is no period
loss."), and the zero-frequency remark at lines 1727-1731 (radial component solenoidal, axial
component a gradient). The target is `CylinderHelmholtzLr` of `Sub/T12.lean`.

## Why the target splits this way

`CylinderHelmholtzLr` asks for (i) existence of a Helmholtz decomposition `F = P F + (F - P F)` of
every `c`-periodic `F ∈ L^r(dq/c dη)`, `1 < r < ∞`, with a bound uniform in `c`, and (ii) a
*linear* (a.e.) choice `P`. The linear choice comes from **uniqueness** of the decomposition:

* `CylHelmholtzExists`: for every `F` there is some `G` with `IsCylHelmholtz` and the bound;
* `CylHelmholtzUnique`: a `c`-periodic `D ∈ L^r` that is weakly divergence free (against
  `CylTest`) and orthogonal to `CylSolTest` vanishes a.e.

Proved here: `cylinderHelmholtzLr_of : CylHelmholtzExists → CylHelmholtzUnique →
CylinderHelmholtzLr` (choose `P F` with `Classical.choose`; apply uniqueness to
`P (F₁ + a F₂) - (P F₁ + a P F₂)`, which is `CylLp`, weakly divergence free and orthogonal to
`CylSolTest` because both conditions are linear in the pair `(F, G)`).

## Sub-leaves (each a true classical statement, see the task specs)

* `PlaneHelmholtzLr` (planar Calderon-Zygmund, `L² ∩ L^r` Leray projection on `ℝ²`; the `N = 2`
  copy of `Lib/LerayLp`);
* `PlanePeriodicLimit` (the "cutoff to `N` cells, average, `N → ∞`" transfer of SP 1933-1935:
  a periodic `G` with `IsPlaneHelmholtz F G`, bound uniform in `c`; uses `PlaneHelmholtzLr`);
* `CylOfPlaneProps` (for periodic `F, G ∈ L^r(cell)`: `IsPlaneHelmholtz F G → IsCylHelmholtz c r F G`,
  by the partition of unity `Σ_n θ(q - n c) = 1`, the stream-function decomposition of a periodic
  solenoidal test, and `L^r(ℝ_η)`-integrability for the zero mode);
* `CylDivCurlFreeZero` (a bounded periodic `C^∞` field with `div = 0 = curl`, in `L^r(cell)`,
  vanishes: Liouville for the periodic holomorphic function `u - i v`) and `CylHelmholtzUnique`
  (mollification reduces to it);
* `CylHelmholtzExists` (from the three previous leaves: truncate `F` to `|F| ≤ n`, `|η| ≤ n`,
  apply `PlanePeriodicLimit` + `CylOfPlaneProps`, and extend by density using uniqueness to see
  that the decompositions of `F_n - F_m` are `G_n - G_m`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-! ## Planar tests and the planar Helmholtz pair -/

/-- A scalar test on the plane `(q, η)`: smooth with compact support. -/
structure PlaneTest (φ : ℝ × ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ φ
  compact : HasCompactSupport φ

/-- A divergence-free vector test field on the plane (`∂_qΨ_0 + ∂_ηΨ_1 = 0`), smooth with compact
support. -/
structure PlaneSolTest (Ψ : ℝ × ℝ → Fin 2 → ℝ) : Prop where
  comp : ∀ i : Fin 2, PlaneTest (fun z => Ψ z i)
  div_free : ∀ z : ℝ × ℝ,
    fderiv ℝ (fun y => Ψ y 0) z (1, 0) + fderiv ℝ (fun y => Ψ y 1) z (0, 1) = 0

/-- `G` is a planar Helmholtz companion of `F` (no periodicity, no integrability of `F, G` over the
plane is assumed; the pairings are with compactly supported tests): `G` is weakly divergence free
(`∫ G·∇φ = 0` for planar tests `φ`) and `F - G` annihilates every planar solenoidal test (it is a
gradient), the pairings being integrable. -/
def IsPlaneHelmholtz (F G : ℝ × ℝ → CMerid) : Prop :=
  (∀ φ : ℝ × ℝ → ℝ, PlaneTest φ →
      Integrable (fun z => G z 0 * (fderiv ℝ φ z (1, 0) : ℂ) + G z 1 * (fderiv ℝ φ z (0, 1) : ℂ)) ∧
        ∫ z, (G z 0 * (fderiv ℝ φ z (1, 0) : ℂ) + G z 1 * (fderiv ℝ φ z (0, 1) : ℂ)) = 0) ∧
    (∀ Ψ : ℝ × ℝ → Fin 2 → ℝ, PlaneSolTest Ψ →
      Integrable (fun z => ∑ i : Fin 2, (F z i - G z i) * (Ψ z i : ℂ)) ∧
        ∫ z, ∑ i : Fin 2, (F z i - G z i) * (Ψ z i : ℂ) = 0)

/-! ## The sub-leaves -/

/-- **Leaf `PartII-b:T12/1/1`** (planar Calderon-Zygmund input, INF01; Grafakos *Classical Fourier
Analysis* Cor. 5.2.8; SP 1923-1926 for the use of `P_0`): the Leray (Helmholtz) projection of the
plane is bounded on `L^r(ℝ²; ℂ²)` for `1 < r < ∞` and a contraction on `L²`. Stated on
`F ∈ L² ∩ L^r` (the decomposition is the `L²` Leray projection, which is also `L^r` bounded):
there is `G ∈ L² ∩ L^r` with `‖G‖₂ ≤ ‖F‖₂`, `‖G‖_r ≤ C_r ‖F‖_r`, `G` weakly divergence free and
`F - G` orthogonal to compactly supported smooth solenoidal fields. Proof: the `N = 2` copy of
`Lib/LerayLp` (Riesz kernels `∂_i∂_j (-Δ)⁻¹`, Hormander condition, `L²` boundedness, CZ to `L^r`
via `Lib/CZCore`, then the test-level formula `G = F + ∇ N * div F`). -/
def PlaneHelmholtzLr : Prop :=
  ∀ r : ℝ, 1 < r → ∃ C : ℝ, 0 < C ∧ ∀ F : ℝ × ℝ → CMerid,
    MemLp F 2 volume → MemLp F (ENNReal.ofReal r) volume →
      ∃ G : ℝ × ℝ → CMerid, MemLp G 2 volume ∧ MemLp G (ENNReal.ofReal r) volume ∧
        eLpNorm G 2 volume ≤ eLpNorm F 2 volume ∧
        eLpNorm G (ENNReal.ofReal r) volume ≤
          ENNReal.ofReal C * eLpNorm F (ENNReal.ofReal r) volume ∧
        IsPlaneHelmholtz F G

/-- **Leaf `PartII-b:T12/1/2`** (Liouville core of the uniqueness): a bounded `C^∞` field
`(u, v)` on the plane which is `c`-periodic in `q`, lies in `L^r(dq/c dη)` (infinite measure, so
constants are excluded), and is divergence free and curl free vanishes. Proof: `f = u - i v`
satisfies the Cauchy-Riemann equations, so `f` is holomorphic in `q + iη`, `c`-periodic; the
function `g(w) = f((c/2πi) log w)` is holomorphic and bounded on `ℂ \ {0}`, the singularity at `0`
is removable (`Complex.differentiableOn_update_limUnder_of_bddAbove`), Liouville
(`Differentiable.apply_eq_apply_of_bounded`) makes `g` constant, and a nonzero constant is not in
`L^r(Cyl.avgμ c)` because `Cyl.avgμ c univ = ∞`. -/
def CylDivCurlFreeZero : Prop :=
  ∀ (c r : ℝ) (u v : ℝ × ℝ → ℝ), 0 < c → 1 ≤ r →
    ContDiff ℝ ∞ u → ContDiff ℝ ∞ v →
    (∀ z : ℝ × ℝ, u (z.1 + c, z.2) = u z) → (∀ z : ℝ × ℝ, v (z.1 + c, z.2) = v z) →
    (∃ M : ℝ, ∀ z : ℝ × ℝ, |u z| ≤ M ∧ |v z| ≤ M) →
    MemLp u (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c) →
    MemLp v (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c) →
    (∀ z : ℝ × ℝ, fderiv ℝ u z (1, 0) + fderiv ℝ v z (0, 1) = 0) →
    (∀ z : ℝ × ℝ, fderiv ℝ v z (1, 0) - fderiv ℝ u z (0, 1) = 0) →
      ∀ z : ℝ × ℝ, u z = 0 ∧ v z = 0

/-- **Leaf `PartII-b:T12/1/3`** (uniqueness of the cylinder Helmholtz decomposition; makes the
choice of `P` a.e. linear). A `c`-periodic `D ∈ L^r(dq/c dη)`, `1 < r`, which is weakly divergence
free (`∫ D·∇φ = 0` for every `CylTest φ`) and orthogonal to every `CylSolTest` vanishes a.e.
Proof: take real and imaginary parts (the tests are real); mollify, `D_ε = D * ρ_ε` is smooth,
`c`-periodic, bounded (Holder on three cells) and in `L^r(avgμ c)`; the mollified tests
`φ * ρ̌_ε`, `Ψ * ρ̌_ε` are again `CylTest`, `CylSolTest`, so `∫ D_ε·∇φ = 0` and
`∫ D_ε·∇^⊥φ = 0` for all `φ`, i.e. `div D_ε = 0 = curl D_ε` pointwise; `CylDivCurlFreeZero` gives
`D_ε = 0`; `D_ε → D` in `L^r_loc` gives `D = 0` a.e. -/
def CylHelmholtzUnique : Prop :=
  ∀ c r : ℝ, 0 < c → 1 < r → ∀ D : ℝ × ℝ → CMerid, CylLp c r D →
    (∀ φ : ℝ × ℝ → ℝ, CylTest c φ →
      ∫ z, (D z 0 * (fderiv ℝ φ z (1, 0) : ℂ) + D z 1 * (fderiv ℝ φ z (0, 1) : ℂ))
        ∂(UnforcedLeray.Cyl.avgμ c) = 0) →
    (∀ Ψ : ℝ × ℝ → Fin 2 → ℝ, CylSolTest c Ψ →
      ∫ z, ∑ i : Fin 2, D z i * (Ψ z i : ℂ) ∂(UnforcedLeray.Cyl.avgμ c) = 0) →
      D =ᵐ[UnforcedLeray.Cyl.avgμ c] 0

/-- **Leaf `PartII-b:T12/1/4`** (SP 1933-1935: "cutoff of `N` repeated cells, dividing its `r`-th
power by `N`, letting `N → ∞`"; uses `PlaneHelmholtzLr`): for `c`-periodic `F` in
`L^2 ∩ L^r(dq/c dη)` there is a `c`-periodic `G ∈ L^r(dq/c dη)` with `IsPlaneHelmholtz F G` and
`‖G‖_{L^r(avgμ c)} ≤ C_r ‖F‖_{L^r(avgμ c)}`, `C_r` independent of `c`. Proof sketch: `F_N = 1_{|q| < Nc/2} F`,
`G_N` its planar projection (`‖G_N‖_{L^r(ℝ²)}^r ≤ C^r N c ‖F‖^r_{L^r(avgμ c)}`, same in `L²`);
`H_N = N⁻¹ Σ_{|j| ≤ N} G_N(· + j c e_q)` is bounded in `L²` and `L^r` on every window `|q| < M c`
uniformly in `N`, weakly divergence free, `F`-orthogonal in the limit, and almost periodic
(`‖H_N - H_N(· + c e_q)‖ ≲ N^{-1/r'}`, here `r > 1` is used); extract an `L²_loc` weak limit
(`Infra/WeaklyNullCompact/Extraction.lean`, diagonal over windows), fold it to an everywhere
periodic representative, and get the `L^r` bound from norming
(`Lib/CZCore/Norming.lean`, `eLpNorm_le_of_forall_test_pairing_of_memLp_two`). -/
def PlanePeriodicLimit : Prop :=
  ∀ r : ℝ, 1 < r → ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, 0 < c → ∀ F : ℝ × ℝ → CMerid,
    CylLp c r F → CylLp c 2 F →
      ∃ G : ℝ × ℝ → CMerid, CylLp c r G ∧ IsPlaneHelmholtz F G ∧
        eLpNorm G (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c) ≤
          ENNReal.ofReal C * eLpNorm F (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c)

/-- **Leaf `PartII-b:T12/1/5`** (planar to cylinder properties, SP 1670/1727-1731): for
`c`-periodic `F, G ∈ L^r(dq/c dη)`, a planar Helmholtz pair is a cylinder Helmholtz pair.
Proof: (a) for a `CylTest φ` apply planar weak solenoidality to `θ(q) φ`
(`CellPart.exists_partition_of_derivs hc`: `Σ_n θ(q - n c) = 1`, `Σ_n θ'(q - n c) = 0`) and unfold the
periodic integrand (`Lib/CylinderB/Periodize.lean`, `CoordPeriodicUnfold`); (b) a `CylSolTest Ψ`
has constant flux `m = ∫ Ψ_0 dη`, so `Ψ = ∇^⊥Φ + m (χ(η), 0)` with `Φ(q, η) = ∫_{-∞}^η (Ψ_0 - m χ)`
smooth, periodic, compactly supported in `η`; test `∇^⊥(θΦ)` for the first part; for the second,
the `q`-average `e(η)` of `(F - G)_0` is in `L^r(ℝ)` and `∫ e ζ' = 0` for all `ζ ∈ C_c^∞(ℝ)` (test
`∇^⊥(θ(q) ζ(η))`), so `e` is a.e. constant and hence `0`. -/
def CylOfPlaneProps : Prop :=
  ∀ c r : ℝ, 0 < c → 1 < r → ∀ F G : ℝ × ℝ → CMerid, CylLp c r F → CylLp c r G →
    IsPlaneHelmholtz F G → IsCylHelmholtz c r F G

/-- **Leaf `PartII-b:T12/1/6`** (existence of the cylinder Helmholtz decomposition with a
`c`-uniform bound; proved from `PlanePeriodicLimit`, `CylOfPlaneProps`, `CylHelmholtzUnique` by
truncation and density): for every `c`-periodic `F ∈ L^r(dq/c dη)` there is `G` with
`IsCylHelmholtz c r F G` and `‖G‖_r ≤ C_r ‖F‖_r`. -/
def CylHelmholtzExists : Prop :=
  ∀ r : ℝ, 1 < r → ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, 0 < c → ∀ F : ℝ × ℝ → CMerid, CylLp c r F →
    ∃ G : ℝ × ℝ → CMerid, IsCylHelmholtz c r F G ∧
      eLpNorm G (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c) ≤
        ENNReal.ofReal C * eLpNorm F (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c)

/-! ## Closure of `CylLp` under linear combinations -/

theorem cylLp_add {c r : ℝ} {F₁ F₂ : ℝ × ℝ → CMerid} (h₁ : CylLp c r F₁) (h₂ : CylLp c r F₂) :
    CylLp c r (F₁ + F₂) := by
  refine ⟨fun z => ?_, h₁.2.add h₂.2⟩
  simp [h₁.1 z, h₂.1 z]

theorem cylLp_sub {c r : ℝ} {F₁ F₂ : ℝ × ℝ → CMerid} (h₁ : CylLp c r F₁) (h₂ : CylLp c r F₂) :
    CylLp c r (F₁ - F₂) := by
  refine ⟨fun z => ?_, h₁.2.sub h₂.2⟩
  simp [h₁.1 z, h₂.1 z]

theorem cylLp_smul {c r : ℝ} (a : ℂ) {F : ℝ × ℝ → CMerid} (h : CylLp c r F) :
    CylLp c r (a • F) := by
  refine ⟨fun z => ?_, h.2.const_smul a⟩
  simp [h.1 z]

/-! ## Conditional assembly -/

theorem integral_comb_sub_add {α : Type*} [MeasurableSpace α] {μ : Measure α} {A B C : α → ℂ}
    (a : ℂ) (iA : Integrable A μ) (iB : Integrable B μ) (iC : Integrable C μ) :
    ∫ z, (A z - (B z + a * C z)) ∂μ = ∫ z, A z ∂μ - (∫ z, B z ∂μ + a * ∫ z, C z ∂μ) := by
  have iBC : Integrable (fun z => B z + a * C z) μ := iB.add (iC.const_mul a)
  have h1 := integral_sub iA iBC
  have h2 := integral_add iB (iC.const_mul a)
  rw [h1, h2, integral_const_mul]

theorem integral_comb_neg_add {α : Type*} [MeasurableSpace α] {μ : Measure α} {A B C : α → ℂ}
    (a : ℂ) (iA : Integrable A μ) (iB : Integrable B μ) (iC : Integrable C μ) :
    ∫ z, (-A z + B z + a * C z) ∂μ = -∫ z, A z ∂μ + ∫ z, B z ∂μ + a * ∫ z, C z ∂μ := by
  have iAB : Integrable (fun z => -A z + B z) μ := iA.neg.add iB
  have h1 := integral_add iAB (iC.const_mul a)
  have iAn : Integrable (fun z => -A z) μ := iA.neg
  have h2 := integral_add iAn iB
  rw [h1, h2, integral_neg, integral_const_mul]

/-- **`PartII-b:T12/1`, conditional**: existence with a uniform bound, plus uniqueness, give the
`c`-uniform a.e. linear Helmholtz projection `P_0` on the cylinder. -/
theorem cylinderHelmholtzLr_of (h2 : CylHelmholtzExists) (h3 : CylHelmholtzUnique) :
    CylinderHelmholtzLr := by
  intro r hr
  obtain ⟨C, hC, hex⟩ := h2 r hr
  refine ⟨C, hC, fun c hc => ?_⟩
  choose! P hP using hex c hc
  refine ⟨P, hP, fun F₁ F₂ a hF₁ hF₂ => ?_⟩
  have hF : CylLp c r (F₁ + a • F₂) := cylLp_add hF₁ (cylLp_smul a hF₂)
  obtain ⟨⟨hG, ha, hb⟩, -⟩ := hP _ hF
  obtain ⟨⟨hG₁, ha₁, hb₁⟩, -⟩ := hP _ hF₁
  obtain ⟨⟨hG₂, ha₂, hb₂⟩, -⟩ := hP _ hF₂
  have hDL : CylLp c r (P (F₁ + a • F₂) - (P F₁ + a • P F₂)) :=
    cylLp_sub hG (cylLp_add hG₁ (cylLp_smul a hG₂))
  have hae := h3 c r hc hr _ hDL ?_ ?_
  · filter_upwards [hae] with z hz
    have hz' : (P (F₁ + a • F₂) - (P F₁ + a • P F₂)) z = 0 := hz
    exact sub_eq_zero.1 hz'
  · intro φ hφ
    obtain ⟨iA, eA⟩ := ha φ hφ
    obtain ⟨iB, eB⟩ := ha₁ φ hφ
    obtain ⟨iC, eC⟩ := ha₂ φ hφ
    have hfun : (fun z => (P (F₁ + a • F₂) - (P F₁ + a • P F₂)) z 0 *
          (fderiv ℝ φ z (1, 0) : ℂ) +
        (P (F₁ + a • F₂) - (P F₁ + a • P F₂)) z 1 * (fderiv ℝ φ z (0, 1) : ℂ)) =
        fun z => (P (F₁ + a • F₂) z 0 * (fderiv ℝ φ z (1, 0) : ℂ) +
            P (F₁ + a • F₂) z 1 * (fderiv ℝ φ z (0, 1) : ℂ)) -
          ((P F₁ z 0 * (fderiv ℝ φ z (1, 0) : ℂ) + P F₁ z 1 * (fderiv ℝ φ z (0, 1) : ℂ)) +
            a * (P F₂ z 0 * (fderiv ℝ φ z (1, 0) : ℂ) +
              P F₂ z 1 * (fderiv ℝ φ z (0, 1) : ℂ))) := by
      funext z
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, PiLp.sub_apply, PiLp.add_apply,
        PiLp.smul_apply, smul_eq_mul]
      ring
    rw [hfun, integral_comb_sub_add a iA iB iC, eA, eB, eC]
    simp
  · intro Ψ hΨ
    obtain ⟨iA, eA⟩ := hb Ψ hΨ
    obtain ⟨iB, eB⟩ := hb₁ Ψ hΨ
    obtain ⟨iC, eC⟩ := hb₂ Ψ hΨ
    have hfun : (fun z => ∑ i : Fin 2, (P (F₁ + a • F₂) - (P F₁ + a • P F₂)) z i * (Ψ z i : ℂ)) =
        fun z => -(∑ i : Fin 2, ((F₁ + a • F₂) z i - P (F₁ + a • F₂) z i) * (Ψ z i : ℂ)) +
          (∑ i : Fin 2, (F₁ z i - P F₁ z i) * (Ψ z i : ℂ)) +
          a * ∑ i : Fin 2, (F₂ z i - P F₂ z i) * (Ψ z i : ℂ) := by
      funext z
      simp only [Fin.sum_univ_two, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, PiLp.sub_apply,
        PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    rw [hfun, integral_comb_neg_add a iA iB iC, eA, eB, eC]
    simp

end UnforcedLeray.Short.IIb

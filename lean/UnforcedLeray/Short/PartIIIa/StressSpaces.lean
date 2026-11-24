import UnforcedLeray.Short.PartIIIa.Defs
import UnforcedLeray.Short.PartIIb.ExactSplit

/-!
# Part III-a, module `stress-spaces.tex` (SP 2664-2817): the thin/repair stress spaces

Definitions of `H`, `H_T`, `Z_1`, `Z`, the split multiplier, and the source's displayed results
`stress-short:lifts`, `:coefficients`, `:transverse`, `:multiplier`, `:moment` and the
outer-coordinate moment identity, as `Prop`s.

Reused Lean: `Axi.ageμ c a` (measure `s^a ds ⊗ dq/c dη`), `Axi.Nv`, `Axi.NT`, `Axi.chart`,
`Axi.lintegral_Nv_rpow`, `Axi.lintegral_NT_sq` (these already prove the lifts), `Axi.IsMeridTensor`.

Interface with Part II. The background `U = V + r_b`, `V = U_raw + E_ε α_bg`, `r_b` the energy
repair, is constructed in `short-background.tex` (SP 2026-2663), outside this area. The two
displayed bounds that are properties of that construction (`:coefficients`, `:transverse`) are stated over the concrete Part II predicate `IIb.ExactSplitII` (`Short/PartII-b/ExactSplit.lean`;
`(V, r_b)` is the exact split background at the level `p : Params`). Nothing else in this file
depends on it.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-! ## The spaces `H`, `H_T`, `Z_1`, `Z` (SP 2671-2701) -/

/-- Frobenius square of a `3×3` tensor in the component order `(r, φ, z)`. -/
def frobSq (T : Matrix (Fin 3) (Fin 3) ℝ) : ℝ := ∑ a : Fin 3, ∑ b : Fin 3, T a b ^ 2

/-- The transverse weight `W = ⟨η/√(1+s)⟩^{m_Z}` at the chart point `(s, (q, η))` (SP 2696). -/
def transWeight (mZ : ℝ) (p : ℝ × (ℝ × ℝ)) : ℝ :=
  (1 + (p.2.2 / Real.sqrt (1 + p.1)) ^ 2) ^ (mZ / 2)

/-- `‖b‖_H²`, `H = L²(s^{-3/2}dς)`, `dς = ds dq/c dη` (SP 2676-2679). -/
def hNormSq (c : ℝ) (b : ℝ × (ℝ × ℝ) → Merid) : ℝ≥0∞ :=
  ∫⁻ p, ‖b p‖ₑ ^ (2 : ℝ) ∂(ageμ c (-3 / 2))

/-- `‖T‖_{H_T}²`, `H_T = L²(s^{-1/2}dς; Sym_3)` with the Frobenius norm. -/
def htNormSq (c : ℝ) (T : ℝ × (ℝ × ℝ) → Matrix (Fin 3) (Fin 3) ℝ) : ℝ≥0∞ :=
  ∫⁻ p, ENNReal.ofReal (frobSq (T p)) ∂(ageμ c (-1 / 2))

/-- `‖T‖_{Z_1}²`, `Z_1 = L²(s^{-1/2}W²dς)` (SP 2697). -/
def z1NormSq (c mZ : ℝ) (T : ℝ × (ℝ × ℝ) → Matrix (Fin 3) (Fin 3) ℝ) : ℝ≥0∞ :=
  ∫⁻ p, ENNReal.ofReal (transWeight mZ p ^ 2 * frobSq (T p)) ∂(ageμ c (-1 / 2))

/-- The sum norm of `Z = Z_1 ⊕ ρ_b^{-1/2}H_T`: `‖(T₁,T₂)‖_Z = ‖T₁‖_{Z_1} + ρ_b^{-1/2}‖T₂‖_{H_T}`
(SP 2698-2700). -/
def zNorm (c mZ ρb : ℝ) (T₁ T₂ : ℝ × (ℝ × ℝ) → Matrix (Fin 3) (Fin 3) ℝ) : ℝ≥0∞ :=
  z1NormSq c mZ T₁ ^ (1 / 2 : ℝ) +
    ENNReal.ofReal (ρb ^ (-1 / 2 : ℝ)) * htNormSq c T₂ ^ (1 / 2 : ℝ)

/-- A meridional vector as a `(r, φ, z)` vector with zero hoop component. -/
def embedMerid (a : Merid) : Fin 3 → ℝ := ![a 0, 0, a 1]

/-- `a ⊗ b + b ⊗ a` for meridional vectors, as a `3×3` tensor in the order `(r, φ, z)`. -/
def symOuter (a b : Merid) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => embedMerid a i * embedMerid b j + embedMerid b i * embedMerid a j

/-- The meridional chart coefficient `v = s^{-1/2} V` of an axisymmetric no-swirl physical field
`V(τ, y)` (similarity variables), at the chart point `(s, (ξ, η))` with
`ϱ = R/√s`, `y₃ = η/√s`, `τ = 2ξ/R + log s` (SP 2706; inverse of `Axi.chart`). The meridional
components at `y = (ϱ, 0, y₃)` are the coordinates `0` and `2`. -/
def chartCoeff (R : ℝ) (V : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (p : ℝ × (ℝ × ℝ)) : Merid :=
  (Real.sqrt p.1)⁻¹ •
    (!₂[V (2 * p.2.1 / R + Real.log p.1) (!₂[R / Real.sqrt p.1, 0, p.2.2 / Real.sqrt p.1]) 0,
        V (2 * p.2.1 / R + Real.log p.1) (!₂[R / Real.sqrt p.1, 0, p.2.2 / Real.sqrt p.1]) 2] :
      Merid)

/-- The `L²_η L^∞_q` norm at age `s` of the weighted coefficient `W v(s)` (SP 2717). -/
def etaL2QSup (c mZ : ℝ) (v : ℝ × (ℝ × ℝ) → Merid) (s : ℝ) : ℝ≥0∞ :=
  (∫⁻ η : ℝ, (essSup (fun q : ℝ => ENNReal.ofReal (transWeight mZ (s, (q, η))) *
      ‖v (s, (q, η))‖ₑ) (volume.restrict (Ico (-(c / 2)) (c / 2)))) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)

/-! ## The results -/

/-- **`stress-short:lifts`** (SP 2683-2688). With `P = 2εc = 2c/R`, for `c`-periodic measurable
`b` and meridional `c`-periodic measurable `T`:
`‖𝒩_v b‖²_{Y₂} = πR²‖b‖²_H` and `‖𝒩_T T‖²_{Y₂} = πR²‖T‖²_{H_T}`, where `‖·‖²_{Y₂}` is the
phase-normalised `ℝ³`-energy over one period. (Proved by `Axi.lintegral_Nv_rpow`,
`Axi.lintegral_NT_sq`.) -/
def StressLifts : Prop :=
  (∀ R c P : ℝ, 0 < R → 0 < c → P = 2 * c / R →
    ∀ b : ℝ × (ℝ × ℝ) → Merid, Measurable b →
      (∀ s ξ η, b (s, (ξ + c, η)) = b (s, (ξ, η))) →
        (ENNReal.ofReal P)⁻¹ * ∫⁻ τ in Ioc 0 P, ∫⁻ y, ‖Nv R b τ y‖ₑ ^ (2 : ℝ) =
          ENNReal.ofReal (Real.pi * R ^ 2) * hNormSq c b) ∧
  (∀ R c P : ℝ, 0 < R → 0 < c → P = 2 * c / R →
    ∀ T : ℝ × (ℝ × ℝ) → Matrix (Fin 3) (Fin 3) ℝ, (∀ a b, Measurable fun p => T p a b) →
      (∀ p, IsMeridTensor (T p)) →
      (∀ s ξ η, T (s, (ξ + c, η)) = T (s, (ξ, η))) →
        (ENNReal.ofReal P)⁻¹ *
            ∫⁻ τ in Ioc 0 P, ∫⁻ y, ENNReal.ofReal (frobSq (NT R T τ y)) =
          ENNReal.ofReal (Real.pi * R ^ 2) * htNormSq c T)

/-- **`stress-short:coefficients`** (SP 2703-2723), over the concrete Part II predicate
`IIb.ExactSplitII` (`Short/PartII-b/ExactSplit.lean`).  For a window `[d₋, d₊]`, `m_Z > 3/2`
and the repair-bound data `ρ_b = C₀ν^{-k₀}e^{m₀/ν}ε^{3/11}` with `m₀ ≤ 3d₋/11` (so
`e^{m₀/ν}ε^{3/11} ≤ 1`, the sense of "absorbed by `P_ν`"), there are a polynomial `C ν^{-k}`
and `ν₀` such that for every level `p` (`ε = e^{-d/ν}`, `c = ν^{-2}`, `R = ε⁻¹`) with `ν ≤ ν₀` and
every exact split `(V, r_b)` with inlet support `S_in`, the coefficient `v = s^{-1/2}V`
(`chartCoeff p.R V`) satisfies the four displayed bounds, the second for every `S ≥ S_in`.
`V = U_raw + E_εα` contains the inlet, the fixed Gaussian angular-two eigenstream of the frozen
growing pair (SP 2048-2049, 2347-2358, 2385-2387), linear in `p.mode` and cut at `H = Σ/ν`; so a
slow age `Σ > 0` and a growing eigenpair `(λ, q)` are fixed before the constants and the levels
have `p.ageCut = Σ`, `p.mode = q` (as in `IIb.ExactSplitExport`). -/
def StressCoefficients : Prop :=
  ∀ dm dp : ℝ, 0 < dm → ∀ (m0 C0 : ℝ) (k0 : ℕ), 0 < m0 → m0 ≤ 3 * dm / 11 →
  ∀ mZ : ℝ, 3 / 2 < mZ →
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧
    ∀ (p : UnforcedLeray.Cons.C03.Concrete.Params) (d : ℝ),
      UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
    ∀ S_in V rb, UnforcedLeray.Short.IIb.ExactSplitII p
        (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0) S_in V rb →
      let v := chartCoeff p.R V
      (∀ pt : ℝ × (ℝ × ℝ), 0 < pt.1 →
        Real.sqrt pt.1 * transWeight mZ pt * ‖v pt‖ ≤ C * (p.ν⁻¹) ^ k) ∧
      (∀ S, S_in ≤ S → 0 < S → ∀ pt : ℝ × (ℝ × ℝ), S < pt.1 →
        Real.sqrt pt.1 * transWeight mZ pt * ‖v pt‖ ≤
          C * (p.ν⁻¹) ^ k * (S ^ (-1 / 2 : ℝ) + p.ε)) ∧
      (∀ σ, 0 < σ → σ ≤ 1 → ∀ pt : ℝ × (ℝ × ℝ), 0 < pt.1 → pt.1 < σ →
        Real.sqrt pt.1 * transWeight mZ pt * ‖v pt‖ ≤ C * (p.ν⁻¹) ^ k * Real.sqrt σ) ∧
      (∀ s, 0 < s → etaL2QSup p.c mZ v s ≤
        ENNReal.ofReal (C * (p.ν⁻¹) ^ k *
          ((1 + s) ^ (-3 / 4 : ℝ) + p.ε * (1 + s) ^ (-1 / 4 : ℝ))))

/-- **`stress-short:transverse`** (SP 2731-2745), over the concrete `IIb.ExactSplitII` and the
actual train `p.train` of the level.  For `S = ε^{-b}` (`b > 0` fixed) and `D_⊥ > 0` fixed there
are `C_⊥` and `ν₀` such that on `0 < s < S`, `|η| > L_⊥ = C_⊥(c/ν + √S + 1)` (`c = p.c`):
`√s W(|v| + |v_flat|) ≤ e^{-D_⊥/ν}`, `v_flat(s,q,η) = p.train.v s (q,η)` the planar train.
(`s ≤ 0` is excluded: there `√s = 0` and the statement is vacuous junk.) The slow age `Σ > 0` and
the growing eigenpair `(λ, q)` of the inlet are fixed before `C_⊥, ν₀` (SP 2743-2745, "the finite
inlet's stream tail"; 2347-2358), with `p.ageCut = Σ`, `p.mode = q`, as in `StressCoefficients`. -/
def StressTransverse : Prop :=
  ∀ dm dp : ℝ, 0 < dm → ∀ (m0 C0 : ℝ) (k0 : ℕ), 0 < m0 → m0 ≤ 3 * dm / 11 →
  ∀ mZ : ℝ, 3 / 2 < mZ → ∀ bexp Dperp : ℝ, 0 < bexp → 0 < Dperp →
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
    ∃ (Cperp ν₀ : ℝ), 0 < ν₀ ∧
    ∀ (p : UnforcedLeray.Cons.C03.Concrete.Params) (d : ℝ),
      UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
    ∀ S_in V rb, UnforcedLeray.Short.IIb.ExactSplitII p
        (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0) S_in V rb →
      ∀ pt : ℝ × (ℝ × ℝ), 0 < pt.1 → pt.1 < p.ε ^ (-bexp) →
        Cperp * (p.c / p.ν + Real.sqrt (p.ε ^ (-bexp)) + 1) < |pt.2.2| →
        Real.sqrt pt.1 * transWeight mZ pt * (‖chartCoeff p.R V pt‖ + ‖p.train.v pt.1 pt.2‖) ≤
          Real.exp (-Dperp / p.ν)

/-- **`stress-short:multiplier`** (SP 2758-2778), over the concrete `IIb.ExactSplitII`.
The exact split multiplier is `𝓜_U b = (v⊗b + b⊗v, v_b⊗b + b⊗v_b)` (SP 2758-2761) with
`v = s^{-1/2}V` (`chartCoeff p.R V`) and `v_b = s^{-1/2}r_b` (`chartCoeff p.R rb`, so `√s v_b = r_b`
at the chart point; SP 2711, 2775), `ρ_b ≥ sup_τ ‖r_b(τ)‖_∞` (SP 2703-2709).  For a window
`[d₋, d₊]`, `m_Z > 3/2` and the repair-bound data `ρ_b = C₀ν^{-k₀}e^{m₀/ν}ε^{3/11}` (`C₀ > 0`,
`0 < m₀ ≤ 3d₋/11`, as in `StressCoefficients`) there are a polynomial `C ν^{-k}` and `ν₀` such that
at every level `p` of the regime with `ν ≤ ν₀`, for every exact split `(V, r_b)` with inlet support
`S_in`, every measurable positive age weight `w` (SP 2777-2778: "after multiplication of both sides
by any common positive age weight, in particular the gain `g(s)^{-1}`"; `w ≡ 1` is the unweighted
statement) and every measurable `b`:
* `‖w𝓜_U b‖_Z ≤ P_ν‖wb‖_H` (SP 2766-2769, first bound);
* `‖(w𝓜_U b)_2‖_{ρ_b^{-1/2}H_T} ≤ 2√ρ_b‖wb‖_H` (SP 2766-2769, second bound; SP 2775-2776);
* the thin old restriction, `S ≥ S_in`: `‖1_{s>S}w(v⊗b+b⊗v)‖_{Z₁} ≤ P_ν(S^{-1/2}+ε)‖1_{s>S}wb‖_H`
  (SP 2771-2772);
* the thin young restriction, `0 < σ ≤ 1`: `‖1_{s<σ}w(v⊗b+b⊗v)‖_{Z₁} ≤ P_ν√σ‖1_{s<σ}wb‖_H`
  (SP 2771-2772).
As in `StressCoefficients`, the slow age `Σ > 0` and the growing eigenpair `(λ, q)` of the inlet
are fixed before the constants, at the levels with `p.ageCut = Σ`, `p.mode = q`. -/
def StressMultiplier : Prop :=
  ∀ dm dp : ℝ, 0 < dm → ∀ (m0 C0 : ℝ) (k0 : ℕ), 0 < m0 → m0 ≤ 3 * dm / 11 → 0 < C0 →
  ∀ mZ : ℝ, 3 / 2 < mZ →
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧
    ∀ (p : UnforcedLeray.Cons.C03.Concrete.Params) (d : ℝ),
      UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
    ∀ S_in V rb, UnforcedLeray.Short.IIb.ExactSplitII p
        (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0) S_in V rb →
    ∀ w : ℝ → ℝ, Measurable w → (∀ s, 0 < w s) →
    ∀ b : ℝ × (ℝ × ℝ) → Merid, Measurable b →
      let v := chartCoeff p.R V
      let vb := chartCoeff p.R rb
      let ρb := UnforcedLeray.Short.IIb.rhoB p m0 C0 k0
      let wb : ℝ × (ℝ × ℝ) → Merid := fun pt => w pt.1 • b pt
      zNorm p.c mZ ρb (fun pt => w pt.1 • symOuter (v pt) (b pt))
          (fun pt => w pt.1 • symOuter (vb pt) (b pt)) ≤
        ENNReal.ofReal (C * (p.ν⁻¹) ^ k) * hNormSq p.c wb ^ (1 / 2 : ℝ) ∧
      ENNReal.ofReal (ρb ^ (-1 / 2 : ℝ)) *
          htNormSq p.c (fun pt => w pt.1 • symOuter (vb pt) (b pt)) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (2 * ρb ^ (1 / 2 : ℝ)) * hNormSq p.c wb ^ (1 / 2 : ℝ) ∧
      (∀ S, S_in ≤ S → 0 < S →
        z1NormSq p.c mZ
            (fun pt => if S < pt.1 then w pt.1 • symOuter (v pt) (b pt) else 0) ^ (1 / 2 : ℝ) ≤
          ENNReal.ofReal (C * (p.ν⁻¹) ^ k * (S ^ (-1 / 2 : ℝ) + p.ε)) *
            hNormSq p.c (fun pt => if S < pt.1 then wb pt else 0) ^ (1 / 2 : ℝ)) ∧
      (∀ σ, 0 < σ → σ ≤ 1 →
        z1NormSq p.c mZ
            (fun pt => if pt.1 < σ then w pt.1 • symOuter (v pt) (b pt) else 0) ^ (1 / 2 : ℝ) ≤
          ENNReal.ofReal (C * (p.ν⁻¹) ^ k * Real.sqrt σ) *
            hNormSq p.c (fun pt => if pt.1 < σ then wb pt else 0) ^ (1 / 2 : ℝ))

/-- The age-weighted first moment `𝒩₁(1_{s>A}T) = ∫_A^∞ s^{-3/2} ∫ (1+|η|/√s)
‖T(s,·,η)‖_{L²(dq/c)} dη ds` (SP 2747-2752). -/
def firstMoment (c A : ℝ) (T : ℝ × (ℝ × ℝ) → Matrix (Fin 3) (Fin 3) ℝ) : ℝ≥0∞ :=
  ∫⁻ s in Ioi A, ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) *
    ∫⁻ η : ℝ, ENNReal.ofReal (1 + |η| / Real.sqrt s) *
      (∫⁻ q in Ico (-(c / 2)) (c / 2),
        ENNReal.ofReal c⁻¹ * ENNReal.ofReal (frobSq (T (s, (q, η))))) ^ (1 / 2 : ℝ)

/-- **`stress-short:moment`** (SP 2747-2753): for `m_Z > 3/2` there is `C_{m_Z}` with, for all
`c > 0`, `A ≥ 1` and measurable tensors `T`,
`𝒩₁(1_{s>A}T) ≤ C A^{-1/2} ‖1_{s>A}T‖_{Z_1}`. -/
def StressMoment : Prop :=
  ∀ mZ : ℝ, 3 / 2 < mZ → ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ, 0 < c → ∀ A : ℝ, 1 ≤ A →
    ∀ T : ℝ × (ℝ × ℝ) → Matrix (Fin 3) (Fin 3) ℝ, (∀ a b, Measurable fun p => T p a b) →
      firstMoment c A T ≤ ENNReal.ofReal (C * A ^ (-1 / 2 : ℝ)) *
        z1NormSq c mZ (fun p => if A < p.1 then T p else 0) ^ (1 / 2 : ℝ)

/-- **Outer-coordinate moment identity** (SP 2790-2795). With `x' ∈ ℝ²`, `u = |x'|^{-2}`,
`Y = η/√u` and the physical tensor `F = uT`:
`∫ (1+|Y|) ‖F(x',Y,·)‖_{L²(dq/c)} dx' dY = π 𝒩₁(T)`. -/
def OuterMomentIdentity : Prop :=
  ∀ c : ℝ, 0 < c → ∀ T : ℝ × (ℝ × ℝ) → Matrix (Fin 3) (Fin 3) ℝ,
    (∀ a b, Measurable fun p => T p a b) →
      ∫⁻ x' : ℝ × ℝ, ∫⁻ Y : ℝ, ENNReal.ofReal (1 + |Y|) *
        (∫⁻ q in Ico (-(c / 2)) (c / 2), ENNReal.ofReal c⁻¹ *
          ENNReal.ofReal ((x'.1 ^ 2 + x'.2 ^ 2)⁻¹ ^ 2 *
            frobSq (T ((x'.1 ^ 2 + x'.2 ^ 2)⁻¹,
              (q, Y * Real.sqrt ((x'.1 ^ 2 + x'.2 ^ 2)⁻¹)))))) ^ (1 / 2 : ℝ) =
        ENNReal.ofReal Real.pi * firstMoment c 0 T

end UnforcedLeray.Short.IIIa

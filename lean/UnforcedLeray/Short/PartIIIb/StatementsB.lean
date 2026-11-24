import UnforcedLeray.Short.PartIIIb.Basic
import UnforcedLeray.Short.PartIIIb.Scalar
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Data.Matrix.Basic

/-!
# Statements B: young response (4333-4553) and the signed flat return (4554-4732)

Concrete objects (explicit formulas of the source, on their whole carriers):
`aOf`, `zOf` (line 4340), `Fpm` (lines 4368-4372), the matrix norm, the class `𝓑_a` and its norm
(lines 4582-4592), the amplitude `a₀(B)` (lines 4614-4618), `D₀ = diag(12,-3,-9)` and
`r_μ(s)` (lines 4697-4706).

Interface objects (the actual cylinder train of Part III-a): the evolution `𝒰(s,t)`, the
heat-scaled frozen Gaussian pair `q_{±,s}`, `ℓ_{±,s}` (`YoungPkg`), and the three functionals
`B ↦ ℓ_μ(M_B)`, `B ↦ a_{ν,+}(B)`, `B ↦ ∫χ_o s^{-3/2-k/2}(1/c)∫|M_B|` of `FlatPkg`.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory

namespace UnforcedLeray.Short.PartIIIb

/-- `a(s) = 1 + νs` (line 4340). -/
def aOf (ν s : ℝ) : ℝ := 1 + ν * s
/-- `z(s) = s/a(s)` (line 4340). -/
def zOf (ν s : ℝ) : ℝ := s / aOf ν s

/-- `F_±(s,t) = exp[λ_±(z(s)-z(t))] (a(s)/a(t))^{κ_±}`, `(λ_+,κ_+) = (λ,κ)`,
`(λ_-,κ_-) = (λ̄,κ̄)` (lines 4368-4372); `j = true` is `+`. -/
def Fpm (j : Bool) (lam κ : ℂ) (ν s t : ℝ) : ℂ :=
  let l := if j then lam else (starRingEnd ℂ) lam
  let k := if j then κ else (starRingEnd ℂ) κ
  Complex.exp (l * ((zOf ν s - zOf ν t : ℝ) : ℂ)) * ((aOf ν s / aOf ν t : ℝ) : ℂ) ^ k

/-- The evolution package of the young-response section (lines 4338-4372): the complex Banach
space `X_{m,c}` of weighted vorticities, the actual train evolution `𝒰(s,t)`, the heat-scaled
periodized frozen pair `q_{±,s}` and its dual `ℓ_{±,s}`. -/
structure YoungPkg where
  X : Type
  [nX : NormedAddCommGroup X]
  [sX : NormedSpace ℂ X]
  [cX : CompleteSpace X]
  Uev : ℝ → ℝ → X →L[ℂ] X
  q : Bool → ℝ → X
  ell : Bool → ℝ → X →L[ℂ] ℂ

attribute [instance] YoungPkg.nX YoungPkg.sX YoungPkg.cX

/-- `eq:young-frozen-pair` (lines 4407-4412): with `H = Σ/ν`, `T_f = α/ν`,
`𝒰(H,t) = Σ_j F_j(H,t) q_{j,H} ℓ_{j,t} + |F_+(H,t)| O_{X→X}(η_ν)` uniformly for `0 ≤ t ≤ T_f`.
The error is relative to `|F_+(H,t)|` at the same `t` (not `|F_+(H,0)|`): the Duhamel step
(lines 4501-4508) uses `|F_+(H,t)| = |F_+(H,0)| |F_+(t,0)|⁻¹` to produce the weight of the tested
norm. `η_ν = ν + δ_c/ν = O(ν)` (line 4392) is written `C ν`. -/
def YoungFrozenPair (pk : ℕ → YoungPkg) (ν : ℕ → ℝ) (lam κ : ℂ) (Sg α : ℝ) : Prop :=
  ∃ (C : ℝ) (N : ℕ), ∀ n ≥ N, ∀ t ∈ Icc (0 : ℝ) (α / ν n),
    ‖(pk n).Uev (Sg / ν n) t -
        ∑ j : Bool, Fpm j lam κ (ν n) (Sg / ν n) t •
          ((pk n).ell j t).smulRight ((pk n).q j (Sg / ν n))‖ ≤
      C * (ν n) * ‖Fpm true lam κ (ν n) (Sg / ν n) t‖

/-- The zero-entrance Duhamel solution `w(s) = s^{-μ} ∫₀^s t^μ 𝒰(s,t) f(t) dt` (lines 4466-4471)
of `(∂_s + μ/s) w = L(s) w + f`, in the form `H^μ w(H)`. -/
def duhamel (pk : YoungPkg) (μ : ℂ) (f : ℝ → pk.X) (s : ℝ) : pk.X :=
  ∫ t in Ioc 0 s, ((t : ℂ) ^ μ) • (pk.Uev s t) (f t)

/-- The frozen amplitudes `a_{ν,±}(f) = ∫₀^{T_f} t^μ F_±(t,0)⁻¹ ℓ_{±,t} f(t) dt`
(lines 4477-4480). -/
def aFrozen (pk : YoungPkg) (j : Bool) (lam κ : ℂ) (ν : ℝ) (μ : ℂ) (Tf : ℝ) (f : ℝ → pk.X) : ℂ :=
  ∫ t in Ioc 0 Tf, ((t : ℂ) ^ μ) * (Fpm j lam κ ν t 0)⁻¹ * (pk.ell j t) (f t)

/-- The tested source norm `‖f‖_{𝓘_{ν,μ}} = ∫₀^{T_f} t^{Re μ} |F_+(t,0)|⁻¹ ‖f(t)‖ dt`
(line 4475). -/
def testedNorm (pk : YoungPkg) (lam κ : ℂ) (ν : ℝ) (μ : ℂ) (Tf : ℝ) (f : ℝ → pk.X) : ℝ :=
  ∫ t in Ioc 0 Tf, t ^ μ.re * ‖Fpm true lam κ ν t 0‖⁻¹ * ‖f t‖

/-- Young source theorem, Duhamel form (lines 4490-4496):
`H^μ w(H) = a_{ν,+}(f) φ_{ν,+}(H) + a_{ν,-}(f) φ_{ν,-}(H) + r_H`, with
`‖r_H‖ ≤ C η_ν |F_+(H,0)| ‖f‖_𝓘`, where `φ_{ν,±}` are the bare columns `φ_+(s) = 𝒰(s,0) v₀`
(`v₀ = P_c q`, line 4387) and `φ_- = φ̄_+`; `conjX` is the complex conjugation of `X_{m,c}`. -/
def YoungDuhamel (pk : ℕ → YoungPkg) (ν : ℕ → ℝ) (lam κ μ : ℂ) (Sg α : ℝ)
    (v0 : ∀ n, (pk n).X) (conjX : ∀ n, (pk n).X → (pk n).X) : Prop :=
  ∃ (C : ℝ) (N : ℕ), ∀ n ≥ N, ∀ f : ℝ → (pk n).X, 
    ‖duhamel (pk n) μ f (Sg / ν n) -
        (aFrozen (pk n) true lam κ (ν n) μ (α / ν n) f • (pk n).Uev (Sg / ν n) 0 (v0 n)
          + aFrozen (pk n) false lam κ (ν n) μ (α / ν n) f •
              conjX n ((pk n).Uev (Sg / ν n) 0 (v0 n)))‖ ≤
      C * (ν n) * ‖Fpm true lam κ (ν n) (Sg / ν n) 0‖ *
        testedNorm (pk n) lam κ (ν n) μ (α / ν n) f

/-! ## The signed flat return (lines 4554-4732) -/

/-- Entrywise `ℓ¹` matrix norm, standing for `|B|` of the source (any equivalent norm). -/
def matNorm (B : Matrix (Fin 3) (Fin 3) ℝ) : ℝ := ∑ i, ∑ j, |B i j|

/-- Meridional decomposition of `B` in the ordering `(r,φ,z)` (lines 4601-4608):
`β = (B_rr + B_zz)/2`, `d = (B_rr - B_zz)/2`, `e = (B_rz + B_zr)/2`. -/
def Bd (B : Matrix (Fin 3) (Fin 3) ℝ) : ℝ := (B 0 0 - B 2 2) / 2
def Be (B : Matrix (Fin 3) (Fin 3) ℝ) : ℝ := (B 0 2 + B 2 0) / 2

/-- The class `𝓑_a` (lines 4582-4592): measurable real trace-free matrices, no mixed azimuthal
entries, supported in `0 < s < 1.1/ν`, with finite `‖B‖_a = ess sup e^{-as}s^{-3/2}|B(s)|`. -/
def IsBclass (a ν : ℝ) (B : ℝ → Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  (∀ i j, Measurable (fun s => B s i j)) ∧ (∀ s, B s 0 0 + B s 1 1 + B s 2 2 = 0) ∧
  (∀ s, B s 0 1 = 0 ∧ B s 1 0 = 0 ∧ B s 1 2 = 0 ∧ B s 2 1 = 0) ∧
  (∀ s, s ∉ Ioo 0 (1.1 / ν) → B s = 0) ∧
  essSup (fun s => ENNReal.ofReal (Real.exp (-a * s) * s ^ (-(3 / 2 : ℝ)) * matNorm (B s)))
      (volume.restrict (Ioi 0)) < ⊤

/-- `‖B‖_a` (line 4592). -/
def bNorm (a : ℝ) (B : ℝ → Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  (essSup (fun s => ENNReal.ofReal (Real.exp (-a * s) * s ^ (-(3 / 2 : ℝ)) * matNorm (B s)))
      (volume.restrict (Ioi 0))).toReal

/-- The limiting amplitude `a₀(B) = -½ ℓ₊(H₀) ∫₀^∞ t^μ e^{-λt}(d(t) - i e(t)) dt`
(lines 4614-4618). -/
def aZero (lam ell μ : ℂ) (B : ℝ → Matrix (Fin 3) (Fin 3) ℝ) : ℂ :=
  -(1 / 2 : ℂ) * ell * ∫ t in Ioi (0 : ℝ),
    ((t : ℂ) ^ μ) * Complex.exp (-lam * (t : ℂ)) * (((Bd (B t) : ℝ) : ℂ) - Complex.I * ((Be (B t) : ℝ) : ℂ))

/-- `D₀ = diag(12, -3, -9)` (line 4697). -/
def Dzero : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal ![12, -3, -9]

/-- `B_μ(s) = r_μ(s) D₀`, `r_μ = χ_f s^{3/2} + χ_f' s^{5/2}/(μ+5/2)` (lines 4697-4701), for a
cutoff profile `χ̂_f` with derivative `χ̂_f'`, `χ_f(s) = χ̂_f(νs)`. -/
def rMu (chi dchi : ℝ → ℝ) (ν μ s : ℝ) : ℝ :=
  chi (ν * s) * s ^ (3 / 2 : ℝ) + ν * dchi (ν * s) * s ^ (5 / 2 : ℝ) / (μ + 5 / 2)

def Bmu (chi dchi : ℝ → ℝ) (ν μ : ℝ) (s : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  rMu chi dchi ν μ s • Dzero

/-- Functionals of the flat return at one regime (interface): `ellMu B = ℓ_μ(M_B)`,
`aNu B = a_{ν,+}(B)`, and `moment k B = ∫χ_o s^{-3/2-k/2}(1/c)∫_cell |M_B| dq dη ds`. -/
structure FlatPkg where
  ellMu : (ℝ → Matrix (Fin 3) (Fin 3) ℝ) → ℝ
  aNu : (ℝ → Matrix (Fin 3) (Fin 3) ℝ) → ℂ
  moment : ℕ → (ℝ → Matrix (Fin 3) (Fin 3) ℝ) → ℝ

/-- `flat-return:class-amplitude` (lines 4624-4626): `|a_{ν,+}(B) - a₀(B)| ≤ C η_ν ‖B‖_a`
(`η_ν = O(ν)`), uniformly on `𝓑_a`. -/
def FlatClassAmplitude (pk : ℕ → FlatPkg) (ν : ℕ → ℝ) (lam ell μ : ℂ) (a : ℝ) : Prop :=
  ∃ (C : ℝ) (N : ℕ), ∀ n ≥ N, ∀ B, IsBclass a (ν n) B →
    ‖(pk n).aNu B - aZero lam ell μ B‖ ≤ C * ν n * bNorm a B

/-- `flat-return:all-moments` (lines 4637-4640): for `k = 0, 1`,
`∫χ_o s^{-3/2-k/2}(1/c)∫|M_B| ≤ C 𝒜_ν ν^k ‖B‖_a`, `𝒜_ν = |N_ν| ν^{3+2μ}/c = |N_ν| ν^{5+2μ}`. -/
def FlatAllMoments (pk : ℕ → FlatPkg) (ν : ℕ → ℝ) (lam κ : ℂ) (μ a : ℝ) : Prop :=
  ∃ (C : ℝ) (N : ℕ), ∀ n ≥ N, ∀ k : ℕ, k ≤ 1 → ∀ B, IsBclass a (ν n) B →
    (pk n).moment k B ≤ C * (‖Nnu lam κ (ν n)‖ * ν n ^ (5 + 2 * μ)) * ν n ^ k * bNorm a B

/-- The scalar estimate of `flat-return` (lines 4628-4632): for every `0 < γ' < γ`,
`|ℓ_μ(M_B) + (3π/16)(ε³ν^{3+2μ}/c) Re[i a₀(B) N_ν J(μ)]| ≤
 C A_*[ω_can + η_ν + P_ν e^{-γ'/√ν}] ‖B‖_a`, with `A_* = ε³|N_ν|ν^{5+2μ}`. -/
def FlatScalarEstimate (pk : ℕ → FlatPkg) (ν ε3 : ℕ → ℝ) (lam κ ell : ℂ) (J : ℂ → ℂ)
    (μ a : ℝ) : Prop :=
  ∀ γ' : ℝ, 0 < γ' → γ' < lam.re →
    ∃ (ωcan : ℕ → ℝ) (C : ℝ) (k : ℕ) (N : ℕ), Tendsto ωcan atTop (𝓝 0) ∧
      ∀ n ≥ N, ∀ B, IsBclass a (ν n) B →
        |(pk n).ellMu B + (3 * Real.pi / 16) * (ε3 n * ν n ^ (5 + 2 * μ)) *
            (Complex.I * aZero lam ell (μ : ℂ) B * Nnu lam κ (ν n) * J (μ : ℂ)).re| ≤
          C * (ε3 n * ‖Nnu lam κ (ν n)‖ * ν n ^ (5 + 2 * μ)) *
            (ωcan n + ν n + (ν n)⁻¹ ^ k * Real.exp (-γ' / Real.sqrt (ν n))) * bNorm a B

/-- `flat-return:coefficient` (Corollary, lines 4697-4712): for the unit source `B_μ` there is
`b > 0` with `|ℓ_μ(M_μ) - 2ε³ν^{5+2μ} Re[𝒞(μ) N_ν]| ≤
 C A_*[ω_can + η_ν + P e^{-b/ν} + P e^{-γ'/√ν}]`. -/
def FlatCoefficient (pk : ℕ → FlatPkg) (ν ε3 : ℕ → ℝ) (lam κ ell : ℂ) (J : ℂ → ℂ)
    (chi dchi : ℝ → ℝ) (μ : ℝ) : Prop :=
  ∃ (ωcan : ℕ → ℝ) (C : ℝ) (k : ℕ) (b γ' : ℝ) (N : ℕ), Tendsto ωcan atTop (𝓝 0) ∧
    0 < b ∧ 0 < γ' ∧ γ' < lam.re ∧
    ∀ n ≥ N,
      |(pk n).ellMu (Bmu chi dchi (ν n) μ) -
          unitResp lam κ (mellinC lam ell J) (ε3 n) (ν n) μ| ≤
        C * (ε3 n * ‖Nnu lam κ (ν n)‖ * ν n ^ (5 + 2 * μ)) *
          (ωcan n + ν n + (ν n)⁻¹ ^ k * Real.exp (-b / ν n)
            + (ν n)⁻¹ ^ k * Real.exp (-γ' / Real.sqrt (ν n)))

end UnforcedLeray.Short.PartIIIb

import UnforcedLeray.Short.PartIIIa.Defs

/-!
# Part III-a, module `separated-kernels.tex` (SP 3582-3860)

The heat-Leray kernel `K_t`, the explicit negative response `W_μ = -S_μ T`
(`sep:resolvent`, SP 3611-3617) of a tensor `T` supported in the radial disk `|z'| ≤ r_o`
(`z'` the horizontal part of `z ∈ ℝ³`), observed at `|y'| ≥ r_i > r_o`, and the results
`sep:kernel`, `sep:young` (with the pointwise form), `sep:repair-point`, `sep:repair-global`, `sep:repair-energy`,
`sep:thin-global`, `sep:mean-comparison`, `sep:phase-sup`.

Conventions. `(∇K : T)_i = ∑_{jk} ∂_kK_{ij} T_{jk}` (index placement is immaterial for every
estimate, which only uses magnitudes of order-four kernels). Phase norms are normalised on
`𝕋_P = (0,P]`; `T` is `P`-periodic in `τ`. `D = r_i - r_o`. `Space` is `ℝ³`; its coordinates
`0,1` are horizontal, `2` vertical.

Omitted (documented in the report): the stream-cutoff statements (`𝒞_χ`, `X`, `Y`, SP 3687-3730),
`sep:phase-age`, `sep:mean-age` (the age-band variants of `sep:mean-comparison`) and the
transport-identity upgrades (`sep:phase-sup` is stated in its scalar form).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-! ## The heat-Leray kernel (SP 3600-3610) -/

/-- The three-dimensional heat kernel `G_t(x) = (4πt)^{-3/2}e^{-|x|²/(4t)}`, `t > 0`. -/
def heatG (t : ℝ) (x : Space) : ℝ :=
  (4 * Real.pi * t) ^ (-3 / 2 : ℝ) * Real.exp (-‖x‖ ^ 2 / (4 * t))

/-- `∫_t^∞ G_a(x) da` (`t > 0`). -/
def heatTail (t : ℝ) (x : Space) : ℝ := ∫ a in Ioi t, heatG a x

/-- The second partial `∂_i∂_j f`. -/
def part2 (f : Space → ℝ) (i j : Fin 3) (x : Space) : ℝ :=
  fderiv ℝ (fun y => fderiv ℝ f y (coordinateVector j)) x (coordinateVector i)

/-- `(K_t)_{ij} = δ_{ij}G_t + ∂_i∂_j ∫_t^∞ G_a da`, `t > 0`. -/
def heatLerayK (t : ℝ) (i j : Fin 3) (x : Space) : ℝ :=
  (if i = j then heatG t x else 0) + part2 (heatTail t) i j x

/-- `K_0 = D²(4π|x|)^{-1}` off the origin. -/
def heatLerayK0 (i j : Fin 3) (x : Space) : ℝ := part2 (fun y => (4 * Real.pi * ‖y‖)⁻¹) i j x

/-- **`sep:kernel`** (SP 3604-3610): for each `j` there is `C_j` with, off the origin,
`|D^j∇K_t(x)| ≤ C_j|x|^{-4-j}` (all `t > 0` and `t = 0`) and
`|D^j(K_t - K_0)(x)| ≤ C_j t|x|^{-5-j}`. -/
def SepKernelBounds : Prop :=
  ∀ j : ℕ, ∃ C : ℝ, ∀ x : Space, x ≠ 0 → ∀ i k : Fin 3,
    (∀ t : ℝ, 0 < t → ‖iteratedFDeriv ℝ (j + 1) (fun y => heatLerayK t i k y) x‖ ≤
        C * ‖x‖ ^ (-4 - (j : ℝ))) ∧
      ‖iteratedFDeriv ℝ (j + 1) (fun y => heatLerayK0 i k y) x‖ ≤ C * ‖x‖ ^ (-4 - (j : ℝ)) ∧
      ∀ t : ℝ, 0 < t → ‖iteratedFDeriv ℝ j (fun y => heatLerayK t i k y - heatLerayK0 i k y) x‖ ≤
        C * t * ‖x‖ ^ (-5 - (j : ℝ))

/-! ## The negative response `W_μ` (SP 3611-3617) -/

/-- The Frobenius norm of a real `3×3` tensor. -/
def tensorNorm (M : Matrix (Fin 3) (Fin 3) ℝ) : ℝ := Real.sqrt (∑ i, ∑ j, M i j ^ 2)

/-- A `P`-periodic measurable tensor source supported in the radial disk `|z'| ≤ r_o`. -/
structure IsSepSource (P rOut : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) : Prop where
  measurable : ∀ i j, Measurable fun p : ℝ × Space => T p.1 p.2 i j
  periodic : ∀ τ z, T (τ + P) z = T τ z
  support : ∀ τ z, rOut < Real.sqrt (z 0 ^ 2 + z 1 ^ 2) → T τ z = 0

/-- `W_μ(y,τ) = -2∫_0^1 λ^{2μ+2}∫ ∇K_{ν(1-λ²)}(y - λz) : T(z, τ + 2 log λ) dz dλ`
(`sep:resolvent`). -/
def sepW (ν : ℝ) (μ : ℂ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (y : Space) (τ : ℝ) :
    Fin 3 → ℂ :=
  fun i => -2 * ∫ l in Ioo (0 : ℝ) 1, (l : ℂ) ^ (2 * μ + 2) *
    ∫ z : Space, ∑ j : Fin 3, ∑ k : Fin 3,
      ((fderiv ℝ (fun x => heatLerayK (ν * (1 - l ^ 2)) i j x) (y - l • z)
        (coordinateVector k) : ℝ) : ℂ) * ((T (τ + 2 * Real.log l) z j k : ℝ) : ℂ)

/-- The mixed norm `‖f‖_{L²_τ L^q_y} = ((1/P)∫_0^P (∫ f^q dy)^{2/q} dτ)^{1/2}`. -/
def ltauLq (P q : ℝ) (f : ℝ → Space → ℝ≥0∞) : ℝ≥0∞ :=
  ((ENNReal.ofReal P)⁻¹ * ∫⁻ τ in Ioc 0 P, (∫⁻ y, f τ y ^ q) ^ (2 / q)) ^ (1 / 2 : ℝ)

/-- The phase norm `‖g‖_{L²_τ}` (normalised) at a fixed point. -/
def ltauAt (P : ℝ) (g : ℝ → ℝ≥0∞) : ℝ≥0∞ :=
  ((ENNReal.ofReal P)⁻¹ * ∫⁻ τ in Ioc 0 P, g τ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)

/-- `|D^jW_μ(y,τ)|`. -/
def wDerivNorm (ν : ℝ) (μ : ℂ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (j : ℕ)
    (τ : ℝ) (y : Space) : ℝ≥0∞ :=
  ‖iteratedFDeriv ℝ j (fun y' => sepW ν μ T y' τ) y‖ₑ

/-- `1_young |D^jW_μ|`: the indicator of the receiver region `|y'| ≥ r_i`. -/
def youngDerivNorm (ν : ℝ) (μ : ℂ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (j : ℕ)
    (rIn : ℝ) (τ : ℝ) (y : Space) : ℝ≥0∞ :=
  if rIn ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2) then wDerivNorm ν μ T j τ y else 0

/-- `|T(z,τ)|` as an extended real. -/
def srcNorm (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (z : Space) : ℝ≥0∞ :=
  ENNReal.ofReal (tensorNorm (T τ z))

/-- **`sep:young`** (SP 3631-3646): `K` compact in `Re μ > -1/4`; `1 ≤ p, b`,
`1 + 1/q = 1/p + 1/b`, `inf_K(2Re μ + 3/p) > 0`. There is `C = C_{K,j,p,q}` (independent of
`ν, D, P`) with
`‖1_young D^jW_μ‖_{L²_τL^q_y} ≤ C D^{-4-j+3/b}‖T‖_{L²_τL^p_y}`. -/
def SepYoung : Prop :=
  ∀ K : Set ℂ, IsCompact K → (∀ μ ∈ K, -(1 / 4) < μ.re) →
    ∀ (j : ℕ) (p q b : ℝ), 1 ≤ p → 1 ≤ b → 1 ≤ q → 1 + 1 / q = 1 / p + 1 / b →
      (∃ δ : ℝ, 0 < δ ∧ ∀ μ ∈ K, δ ≤ 2 * μ.re + 3 / p) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ ν : ℝ, 0 < ν → ∀ μ ∈ K, ∀ rOut rIn P : ℝ, 0 ≤ rOut → rOut < rIn → 0 < P →
        ∀ T, IsSepSource P rOut T →
          ltauLq P q (youngDerivNorm ν μ T j rIn) ≤
            ENNReal.ofReal (C * (rIn - rOut) ^ (-4 - (j : ℝ) + 3 / b)) *
              ltauLq P p (srcNorm T)

/-- **`sep:young`, pointwise version** (SP 3647): `q = ∞`, `b = p'` (`1/p + 1/b = 1`):
`‖D^jW_μ(y,·)‖_{L²_τ} ≤ C D^{-4-j+3/b}‖T‖_{L²_τL^p_y}` at every receiver `|y'| ≥ r_i`. -/
def SepYoungPointwise : Prop :=
  ∀ K : Set ℂ, IsCompact K → (∀ μ ∈ K, -(1 / 4) < μ.re) →
    ∀ (j : ℕ) (p b : ℝ), 1 ≤ p → 1 ≤ b → 1 / p + 1 / b = 1 →
      (∃ δ : ℝ, 0 < δ ∧ ∀ μ ∈ K, δ ≤ 2 * μ.re + 3 / p) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ ν : ℝ, 0 < ν → ∀ μ ∈ K, ∀ rOut rIn P : ℝ, 0 ≤ rOut → rOut < rIn → 0 < P →
        ∀ T, IsSepSource P rOut T → ∀ y : Space, rIn ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2) →
          ltauAt P (fun τ => wDerivNorm ν μ T j τ y) ≤
            ENNReal.ofReal (C * (rIn - rOut) ^ (-4 - (j : ℝ) + 3 / b)) *
              ltauLq P p (srcNorm T)

/-- **`sep:repair-point`, `sep:repair-global`, `sep:repair-energy`** (SP 3648-3668), the
instances `p = 22/19` of `sep:young`:
`‖∇W_μ(y,·)‖_{L²_τ} ≤ C D^{-101/22}‖T‖`, `‖1_young∇W_μ‖_{L²_τL^{22/3}} ≤ C D^{-46/11}‖T‖`,
`‖1_young D^jW_μ‖_{L²_τL²} ≤ C_j D^{-23/11-j}‖T‖`, with `‖T‖ = ‖T‖_{L²_τL^{22/19}}`. -/
def SepRepair : Prop :=
  ∀ K : Set ℂ, IsCompact K → (∀ μ ∈ K, -(1 / 4) < μ.re) →
    (∃ C : ℝ, 0 ≤ C ∧ ∀ ν : ℝ, 0 < ν → ∀ μ ∈ K, ∀ rOut rIn P : ℝ, 0 ≤ rOut → rOut < rIn →
      0 < P → ∀ T, IsSepSource P rOut T → ∀ y : Space, rIn ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2) →
        ltauAt P (fun τ => wDerivNorm ν μ T 1 τ y) ≤
          ENNReal.ofReal (C * (rIn - rOut) ^ (-(101 / 22 : ℝ))) * ltauLq P (22 / 19) (srcNorm T)) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ ν : ℝ, 0 < ν → ∀ μ ∈ K, ∀ rOut rIn P : ℝ, 0 ≤ rOut → rOut < rIn →
      0 < P → ∀ T, IsSepSource P rOut T →
        ltauLq P (22 / 3) (youngDerivNorm ν μ T 1 rIn) ≤
          ENNReal.ofReal (C * (rIn - rOut) ^ (-(46 / 11 : ℝ))) * ltauLq P (22 / 19) (srcNorm T)) ∧
    (∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ ν : ℝ, 0 < ν → ∀ μ ∈ K, ∀ rOut rIn P : ℝ, 0 ≤ rOut →
      rOut < rIn → 0 < P → ∀ T, IsSepSource P rOut T →
        ltauLq P 2 (youngDerivNorm ν μ T j rIn) ≤
          ENNReal.ofReal (C * (rIn - rOut) ^ (-(23 / 11 : ℝ) - (j : ℝ))) *
            ltauLq P (22 / 19) (srcNorm T))

/-- **`sep:thin-global`** (SP 3670-3680): for a thin source with
`∫‖T(z,·)‖_{L²_τ}dz ≤ R²N₀` and `D ≥ c₀R√ν` (`R ≥ 1`), for fixed `q > 1`, `j`, `c₀`:
`‖D^jW_μ‖_{L²_τL^q(young)} ≤ P_ν R^{-2-j+3/q} N₀`, `P_ν = C ν^{-k}`. -/
def SepThinGlobal : Prop :=
  ∀ K : Set ℂ, IsCompact K → (∀ μ ∈ K, -(1 / 4) < μ.re) →
    ∀ (j : ℕ) (q c₀ : ℝ), 1 < q → 0 < c₀ → ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ μ ∈ K, ∀ R N₀ rOut rIn P : ℝ, 1 ≤ R → 0 ≤ N₀ → 0 ≤ rOut →
        rOut < rIn → 0 < P → c₀ * R * Real.sqrt ν ≤ rIn - rOut →
        ∀ T, IsSepSource P rOut T →
          ∫⁻ z : Space, ltauAt P (fun τ => srcNorm T τ z) ≤ ENNReal.ofReal (R ^ 2 * N₀) →
          ltauLq P q (youngDerivNorm ν μ T j rIn) ≤
            ENNReal.ofReal (C * (ν⁻¹) ^ k * R ^ (-2 - (j : ℝ) + 3 / q) * N₀)

/-- **`sep:phase-sup`**, scalar form (SP 3835-3845): if `n ≥ 0` satisfies
`|n(τ₂) - n(τ₁)| ≤ ∫_{τ₁}^{τ₂}(β + κ n)` on `[0,P]` (this is `|d/dτ‖Z‖_q| ≤ ‖BZ‖_q +
(3/(2q))‖Z‖_q` with `κ = 3/(2q)`, `β = ‖BZ‖_q`), then for every `τ ∈ [0,P]`
`n(τ) ≤ (1 + κP) rms(n) + P rms(β)`, `rms(f) = ((1/P)∫_0^P f²)^{1/2}`. -/
def SepPhaseSup : Prop :=
  ∀ (P κ : ℝ), 0 < P → 0 ≤ κ → ∀ n β : ℝ → ℝ,
    (∀ τ, 0 ≤ n τ) → (∀ τ, 0 ≤ β τ) →
    (∀ τ ∈ Icc 0 P, ∀ τ' ∈ Icc 0 P, τ ≤ τ' →
      IntervalIntegrable (fun r => β r + κ * n r) volume τ τ' ∧
        |n τ' - n τ| ≤ ∫ r in τ..τ', (β r + κ * n r)) →
    ∀ τ ∈ Icc 0 P, ENNReal.ofReal (n τ) ≤
      (1 + ENNReal.ofReal (κ * P)) *
          ((ENNReal.ofReal P)⁻¹ * ∫⁻ r in Ioc 0 P, ENNReal.ofReal (n r) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) +
        ENNReal.ofReal P *
          ((ENNReal.ofReal P)⁻¹ * ∫⁻ r in Ioc 0 P, ENNReal.ofReal (β r) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)

/-! ## One phase primitive (SP 3735-3790) -/

/-- The thin tensor in outer coordinates: `T(z,τ) = F(z'/R, z₃, q_ε(|z'|/R, τ))`, `R = ε⁻¹`,
`q_ε(r,τ) = ε⁻¹ log r + τ/(2ε)` (SP 3746-3751); `F(x',Y,q)` is `c`-periodic in `q`. -/
def thinSource (ε : ℝ) (F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ) :
    ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ :=
  fun τ z => F (ε * z 0, ε * z 1) (z 2)
    (ε⁻¹ * Real.log (ε * Real.sqrt (z 0 ^ 2 + z 1 ^ 2)) + τ / (2 * ε))

/-- The normalised phase mean `F̄(x',Y) = c⁻¹∫_0^c F(x',Y,q) dq`. -/
def phaseMean (c : ℝ) (F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ) (x' : ℝ × ℝ) (Y : ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => c⁻¹ * ∫ q in Ioc 0 c, F x' Y q i j

/-- The mean response `V_{μ,0}(x) = -2∫_0^1 λ^{2μ+2}∫ ∇K_0(x - λ(x',0)) : F̄(x',Y) dx' dY dλ`
(SP 3753-3757). -/
def sepVmu0 (μ : ℂ) (Fbar : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ) (x : Space) : Fin 3 → ℂ :=
  fun i => -2 * ∫ l in Ioo (0 : ℝ) 1, (l : ℂ) ^ (2 * μ + 2) *
    ∫ w : (ℝ × ℝ) × ℝ, ∑ j : Fin 3, ∑ k : Fin 3,
      ((fderiv ℝ (fun x' => heatLerayK0 i j x')
        (x - l • (!₂[w.1.1, w.1.2, 0] : Space)) (coordinateVector k) : ℝ) : ℂ) *
        ((Fbar w.1 w.2 j k : ℝ) : ℂ)

/-- The first transverse moment `N₁ = ∫(1+|Y|)‖F(x',Y,·)‖_{L²(dq/c)}dx'dY` (SP 3735-3740). -/
def thinMoment (c : ℝ) (F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ) : ℝ≥0∞ :=
  ∫⁻ w : (ℝ × ℝ) × ℝ, ENNReal.ofReal (1 + |w.2|) *
    (∫⁻ q in Ioc 0 c, ENNReal.ofReal c⁻¹ * ENNReal.ofReal (tensorNorm (F w.1 w.2 q) ^ 2)) ^ (1 / 2 : ℝ)

/-- **`sep:mean-comparison`** (SP 3767-3780): `R = ε⁻¹`, `P = 2εc`; `F` is `c`-periodic in `q`,
measurable, supported in `|x'| ≤ ρ_o`; the receiver has `|x_obs'| ≥ ρ_i > ρ_o`, `y = R x_obs`:
`‖∇_yW_μ(y,·) - ε³∇_xV_{μ,0}(y/R)‖_{L²_τ} ≤ P_ν ε⁴ N₁`, where `P_ν` is a polynomial
(`C(1 + ν⁻¹ + c + ρ_i + ρ_o + (ρ_i - ρ_o)⁻¹)^k`) in the inverse viscosity, the radial endpoints,
their gap and `c`. As everywhere in the source (SP 219-221: `P_ν` is a fixed polynomial in
`ν⁻¹`; the small-viscosity regime `0 < ν ≤ 1`, cf. SP 5008), the viscosity is restricted to
`0 < ν ≤ 1`: the heat error `|D(K_t - K_0)| ≤ Ct|x|^{-6}` (`sep:kernel`) at
`t = νε²(1 - λ²) ≤ ε²` is then of the order `ε` in outer coordinates; for `ν ≫ 1` the bound
fails. -/
def SepMeanComparison : Prop :=
  ∀ K : Set ℂ, IsCompact K → (∀ μ ∈ K, -(1 / 4) < μ.re) → ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧
    ∀ ν c ε ρo ρi : ℝ, 0 < ν → ν ≤ 1 → 0 < c → 0 < ε → ε ≤ 1 → 0 ≤ ρo → ρo < ρi → ∀ μ ∈ K,
      ∀ F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ,
        (∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ × ℝ => F w.1 w.2.1 w.2.2 i j) →
        (∀ x' Y q, F x' Y (q + c) = F x' Y q) →
        (∀ x' Y q, ρo < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → F x' Y q = 0) →
        ∀ xo : Space, ρi ≤ Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) →
          ltauAt (2 * ε * c) (fun τ => ‖fderiv ℝ (fun y => sepW ν μ (thinSource ε F) y τ) (ε⁻¹ • xo) -
              (ε ^ 3 : ℝ) • fderiv ℝ (sepVmu0 μ (phaseMean c F)) xo‖ₑ) ≤
            ENNReal.ofReal (C * (1 + ν⁻¹ + c + ρi + ρo + (ρi - ρo)⁻¹) ^ k * ε ^ 4) *
              thinMoment c F

end UnforcedLeray.Short.IIIa

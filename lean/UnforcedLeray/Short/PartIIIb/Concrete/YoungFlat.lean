import UnforcedLeray.Short.PartIIIb.StatementsB

/-!
# Concrete young-response and flat-return packages (source 4333-4732)

Replaces the free interface `YoungPkg`/`FlatPkg` targets of `StatementsB.lean` (which were false for
degenerate packages, see `Proofs/DeferredYoungFlat.lean`) by

* `YoungLaws`: the structural laws of the objects of source 4338-4350 (evolution law
  `𝒰(s,r)𝒰(r,t) = 𝒰(s,t)`, Gram normalisation `ℓ_{i,s} q_{j,s} = δ_ij` (4345), `q_- = q̄_+`,
  `ℓ_- = ℓ̄_+`, real evolution);
* the hypotheses `0 < ν_n`, `ν_n → 0`, `Re λ > 0`, `0 < α < Σ`, the support/integrability of the
  forcing;
* `YoungBlockEstimates`: the output of the finite-band block estimate with the Gronwall argument
  (source 4376-4411, from Proposition `prop:short-full-clock`), stated at `s = H`, which is the
  only analytic input of the frozen-pair theorem;
* concrete flat functionals `gB`, `aNuC`, `ellMuC`, `momentC` (source 4570-4620) built from the
  young package plus the readout `Mcell` (stress `M_B = v ⊗ b_B + b_B ⊗ v`, `b_B = K_c ξ_B`);
* the flat targets as conditional Props on named source facts.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory

namespace UnforcedLeray.Short.PartIIIb

namespace ConcreteYF

/-- Complement projector `P_{c,t} = 1 - Σ_j q_{j,t} ℓ_{j,t}` (source 4345-4350). -/
def Pc (pk : YoungPkg) (t : ℝ) : pk.X →L[ℂ] pk.X :=
  ContinuousLinearMap.id ℂ pk.X - ∑ j : Bool, (pk.ell j t).smulRight (pk.q j t)

/-- Structural laws of the actual train package (source 4338-4350, 4385-4390).
`conjX` is complex conjugation of `X_{m,c}` (real vorticities). -/
structure YoungLaws (pk : YoungPkg) (conjX : pk.X → pk.X) : Prop where
  refl : ∀ s, pk.Uev s s = ContinuousLinearMap.id ℂ pk.X
  trans : ∀ s r t, 0 ≤ t → t ≤ r → r ≤ s → (pk.Uev s r).comp (pk.Uev r t) = pk.Uev s t
  gram : ∀ s i j, pk.ell i s (pk.q j s) = if i = j then 1 else 0
  conj_add : ∀ x y, conjX (x + y) = conjX x + conjX y
  conj_smul : ∀ (a : ℂ) x, conjX (a • x) = (starRingEnd ℂ a) • conjX x
  conj_norm : ∀ x, ‖conjX x‖ = ‖x‖
  conj_inv : ∀ x, conjX (conjX x) = x
  conj_U : ∀ s t x, conjX (pk.Uev s t x) = pk.Uev s t (conjX x)
  conj_q : ∀ s, pk.q false s = conjX (pk.q true s)
  conj_ell : ∀ s x, pk.ell false s x = (starRingEnd ℂ) (pk.ell true s (conjX x))

/-- Uniform bounds on the frozen pair and on the evolution band (source 4376-4380: heat-scaled
endpoint maps have uniform norms on the finite band `0 ≤ s ≤ H`). -/
def YoungBounded (pk : ℕ → YoungPkg) (ν : ℕ → ℝ) (Sg : ℝ) : Prop :=
  ∃ C : ℝ, ∀ n, ∀ s ∈ Icc (0 : ℝ) (Sg / ν n), ∀ j : Bool,
    ‖(pk n).q j s‖ ≤ C ∧ ‖(pk n).ell j s‖ ≤ C

/-- The block estimates after the Gronwall argument (source 4376-4411), at `s = H = Σ/ν`, for
`0 ≤ t ≤ T_f = α/ν`, relative to `|F_+(H,t)|` and with error `C ν` (`η_ν = O(ν)`):
direct amplitudes `ℓ_{i,H} 𝒰(H,t) q_{j,t} = δ_ij F_j(H,t) + O`, the two couplings
`P_H 𝒰 q_{j,t}`, `ℓ_{i,H} 𝒰 P_t`, and the complement propagation `P_H 𝒰(H,t) P_t`
(exponentially small since `H - t ≥ (Σ-α)/ν`). -/
def YoungBlockEstimates (pk : ℕ → YoungPkg) (ν : ℕ → ℝ) (lam κ : ℂ) (Sg α : ℝ) : Prop :=
  ∃ (C : ℝ) (N : ℕ), ∀ n ≥ N, ∀ t ∈ Icc (0 : ℝ) (α / ν n),
    (∀ i j : Bool,
      ‖(pk n).ell i (Sg / ν n) ((pk n).Uev (Sg / ν n) t ((pk n).q j t)) -
          (if i = j then Fpm j lam κ (ν n) (Sg / ν n) t else 0)‖ ≤
        C * ν n * ‖Fpm true lam κ (ν n) (Sg / ν n) t‖) ∧
    (∀ j : Bool, ‖Pc (pk n) (Sg / ν n) ((pk n).Uev (Sg / ν n) t ((pk n).q j t))‖ ≤
        C * ν n * ‖Fpm true lam κ (ν n) (Sg / ν n) t‖) ∧
    (∀ (i : Bool) (y : (pk n).X), ‖(pk n).ell i (Sg / ν n) ((pk n).Uev (Sg / ν n) t (Pc (pk n) t y))‖ ≤
        C * ν n * ‖Fpm true lam κ (ν n) (Sg / ν n) t‖ * ‖y‖) ∧
    ‖(Pc (pk n) (Sg / ν n)).comp (((pk n).Uev (Sg / ν n) t).comp (Pc (pk n) t))‖ ≤
        C * ν n * ‖Fpm true lam κ (ν n) (Sg / ν n) t‖

/-- Standing hypotheses on the viscosity sequence and band (source 4340-4346). -/
def YoungHyp (ν : ℕ → ℝ) (lam : ℂ) (Sg α : ℝ) : Prop :=
  (∀ n, 0 < ν n) ∧ Tendsto ν atTop (𝓝 0) ∧ 0 < lam.re ∧ 0 < α ∧ α < Sg

/-- `eq:young-frozen-pair` (4407-4412), concrete version: under the laws, bounds, hypotheses and
the block estimates, `YoungFrozenPair` holds, with the error relative to `|F_+(H,t)|` at the same
`t` (this is exactly what `YoungBlockEstimates` gives; no comparison with `|F_+(H,0)|` is made). -/
def YoungFrozenPairC (pk : ℕ → YoungPkg) (conjX : ∀ n, (pk n).X → (pk n).X)
    (ν : ℕ → ℝ) (lam κ : ℂ) (Sg α : ℝ) : Prop :=
  (∀ n, YoungLaws (pk n) (conjX n)) → YoungHyp ν lam Sg α → YoungBounded pk ν Sg →
    YoungBlockEstimates pk ν lam κ Sg α → YoungFrozenPair pk ν lam κ Sg α

/-- Young source theorem (4463-4508), concrete version. The bare column is
`φ_{ν,+}(s) = 𝒰(s,0) v₀` with `v₀ = q_{+,0}`, and `φ_- = conj φ_+` (4417-4426). Forcing `f` is
supported in `0 < s ≤ T_f` (4463), with integrable Duhamel and amplitude integrands, and lies in
the tested class: the integrand of `‖f‖_{𝓘_{ν,μ}} = ∫₀^{T_f} t^{Re μ}|F_+(t,0)|⁻¹‖f(t)‖ dt` is
integrable (the finite tested norm of 4480-4487). The error of the frozen pair at `(H,t)`,
relative to `|F_+(H,t)| = |F_+(H,0)| |F_+(t,0)|⁻¹`, integrates against `t^{Re μ}‖f(t)‖` to
`|F_+(H,0)| ‖f‖_𝓘` (4501-4508). -/
def YoungDuhamelC (pk : ℕ → YoungPkg) (conjX : ∀ n, (pk n).X → (pk n).X)
    (ν : ℕ → ℝ) (lam κ μ : ℂ) (Sg α : ℝ) : Prop :=
  (∀ n, YoungLaws (pk n) (conjX n)) → YoungHyp ν lam Sg α → YoungBounded pk ν Sg →
    YoungFrozenPair pk ν lam κ Sg α →
    ∃ (C : ℝ) (N : ℕ), ∀ n ≥ N, ∀ f : ℝ → (pk n).X,
      (∀ t, α / ν n < t → f t = 0) → (∀ t, t ≤ 0 → f t = 0) →
      Integrable (fun t : ℝ => ((t : ℂ) ^ μ) • ((pk n).Uev (Sg / ν n) t (f t))) (volume.restrict (Ioc 0 (Sg / ν n))) →
      Integrable (fun t : ℝ => ((t : ℂ) ^ μ) * (Fpm true lam κ (ν n) t 0)⁻¹ * ((pk n).ell true t) (f t))
        (volume.restrict (Ioc 0 (α / ν n))) →
      Integrable (fun t : ℝ => ((t : ℂ) ^ μ) * (Fpm false lam κ (ν n) t 0)⁻¹ * ((pk n).ell false t) (f t))
        (volume.restrict (Ioc 0 (α / ν n))) →
      Integrable (fun t : ℝ => t ^ μ.re * ‖Fpm true lam κ (ν n) t 0‖⁻¹ * ‖f t‖)
        (volume.restrict (Ioc 0 (α / ν n))) →
      ‖duhamel (pk n) μ f (Sg / ν n) -
          (aFrozen (pk n) true lam κ (ν n) μ (α / ν n) f • (pk n).Uev (Sg / ν n) 0 ((pk n).q true 0)
            + aFrozen (pk n) false lam κ (ν n) μ (α / ν n) f •
                conjX n ((pk n).Uev (Sg / ν n) 0 ((pk n).q true 0)))‖ ≤
        C * ν n * ‖Fpm true lam κ (ν n) (Sg / ν n) 0‖ * testedNorm (pk n) lam κ (ν n) μ (α / ν n) f

/-! ## The flat return: concrete functionals (source 4570-4620) -/

/-- The concrete flat setting: the young package, the periodized Gaussian sources
`H_{s,c}`, `R_{s,c}` (source 4575-4577) in `X_{m,c}`, the stress readout
`Mcell s ξ = M = v ⊗ K_c ξ + K_c ξ ⊗ v` on the cell as a matrix field in `(q,η)` at age `s`,
the cutoff `χ_o`, the cell size `c` and the amplitude `ε³`. -/
structure FlatSetting where
  pk : YoungPkg
  conjX : pk.X → pk.X
  Hper : ℝ → pk.X
  Rper : ℝ → pk.X
  Mcell : ℝ → pk.X → (ℝ × ℝ → Matrix (Fin 3) (Fin 3) ℝ)
  chiO : ℝ → ℝ
  c : ℝ
  eps3 : ℝ

/-- Meridional trace part `β = (B_rr + B_zz)/2` (source 4601-4608). -/
def Bbeta (B : Matrix (Fin 3) (Fin 3) ℝ) : ℝ := (B 0 0 + B 2 2) / 2

/-- The vorticity source `g_B = -½(d-ie)H - ½(d+ie)H̄ - β R` (source 4605-4608). -/
def FlatSetting.gB (S : FlatSetting) (B : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (s : ℝ) : S.pk.X :=
  (-(1 / 2 : ℂ) * (((Bd (B s) : ℝ) : ℂ) - Complex.I * ((Be (B s) : ℝ) : ℂ))) • S.Hper s
  + (-(1 / 2 : ℂ) * (((Bd (B s) : ℝ) : ℂ) + Complex.I * ((Be (B s) : ℝ) : ℂ))) • S.conjX (S.Hper s)
  - (((Bbeta (B s) : ℝ) : ℂ)) • S.Rper s

/-- `ξ_B(s) = s^{-μ} ∫₀^s t^μ 𝒰(s,t) g_B(t) dt` (source 4610). -/
def FlatSetting.xi (S : FlatSetting) (μ : ℂ) (B : ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (s : ℝ) : S.pk.X :=
  ((s : ℂ) ^ (-μ)) • duhamel S.pk μ (S.gB B) s

/-- `a_{ν,+}(B)` (source 4666-4668). -/
def FlatSetting.aNuC (S : FlatSetting) (lam κ μ : ℂ) (ν : ℝ) (B : ℝ → Matrix (Fin 3) (Fin 3) ℝ) : ℂ :=
  aFrozen S.pk true lam κ ν μ (1.1 / ν) (S.gB B)

/-- The cell average `(1/c) ∫_cell M_{zz}`-type integrals, over `(-c/2,c/2) × ℝ` with Lebesgue
measure, of a matrix field. -/
def cellInt (c : ℝ) (F : ℝ × ℝ → ℝ) : ℝ :=
  c⁻¹ * ∫ p in (Ioo (-c / 2) (c / 2)) ×ˢ (univ : Set ℝ), F p

/-- `I_T(M) = ∫ χ_o s^{-3/2} (1/c) ∫_cell (2 M_zz - M_rr) dq dη ds` (source 4584-4587). -/
def FlatSetting.IT (S : FlatSetting) (M : ℝ → ℝ × ℝ → Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), S.chiO s * s ^ (-(3 / 2 : ℝ)) *
    cellInt S.c (fun p => 2 * M s p 2 2 - M s p 0 0)

/-- `ℓ_μ(M_B) = ε³ I_T(M_B)/(8(μ+3/2))` (source 4586-4587). -/
def FlatSetting.ellMuC (S : FlatSetting) (lam κ : ℂ) (μ : ℝ) (B : ℝ → Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  S.eps3 * S.IT (fun s => S.Mcell s (S.xi (μ : ℂ) B s)) / (8 * (μ + 3 / 2))

/-- `∫ χ_o s^{-3/2-k/2} (1/c) ∫_cell |M_B| dq dη ds` (source 4637-4640), `|·|` = `matNorm`. -/
def FlatSetting.momentC (S : FlatSetting) (lam κ : ℂ) (μ : ℝ) (k : ℕ)
    (B : ℝ → Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), S.chiO s * s ^ (-(3 / 2 : ℝ) - (k : ℝ) / 2) *
    cellInt S.c (fun p => matNorm (S.Mcell s (S.xi (μ : ℂ) B s) p))

/-- The `FlatPkg` of a flat setting. -/
def FlatSetting.toPkg (S : FlatSetting) (lam κ : ℂ) (ν μ : ℝ) : FlatPkg where
  ellMu := S.ellMuC lam κ μ
  aNu := S.aNuC lam κ (μ : ℂ) ν
  moment := fun k => S.momentC lam κ μ k

/-! ## Deferred source facts (inputs), stated for the concrete setting -/

/-- Direct/dual Gaussian comparison (source 4650-4654): `ℓ_{+,νt,c} H_{t,c} = ℓ_+(H₀) + O(νt + c⁻²)`,
`ℓ_{+,νt,c} H̄_{t,c}`, `ℓ_{+,νt,c} R_{t,c} = O(c⁻²)`, for `0 ≤ t ≤ 1.1/ν`, with the frozen pair
of the setting. The cell size is a field of the setting here; `c = ν⁻²` (source 4557), which
turns `c⁻²` into `ν⁴`, is the field `c_eq` of `FlatSettingHyp`. -/
def FlatGaussComparison (S : ℕ → FlatSetting) (ν : ℕ → ℝ) (ell : ℂ) : Prop :=
  ∃ (C : ℝ) (N : ℕ), ∀ n ≥ N, ∀ t ∈ Icc (0 : ℝ) (1.1 / ν n),
    ‖((S n).pk.ell true t) ((S n).Hper t) - ell‖ ≤ C * (ν n * t + (S n).c⁻¹ ^ 2) ∧
    ‖((S n).pk.ell true t) ((S n).conjX ((S n).Hper t))‖ ≤ C * (S n).c⁻¹ ^ 2 ∧
    ‖((S n).pk.ell true t) ((S n).Rper t)‖ ≤ C * (S n).c⁻¹ ^ 2

/-- Old-output anisotropy law (source 4524-4534, real form 4719-4722): for the setting, with
`u_o = ν^{-3/2}`, the late-old tested stress equals
`(3π/(2c))(μ+3/2)ν^{3+2μ} Im[a_{ν,+}(B) N_ν J(μ)] + O(𝒜_ν(η_ν + ω_can))‖B‖_a`
uniformly on `𝓑_a`; here `I_T` is restricted to `s ≥ u_o`, expressed through `chiO` replaced by the
indicator. -/
def FlatOldAnisotropy (S : ℕ → FlatSetting) (ν : ℕ → ℝ) (lam κ : ℂ) (J : ℂ → ℂ)
    (μ a : ℝ) : Prop :=
  ∃ (ωcan : ℕ → ℝ) (C : ℝ) (N : ℕ), Tendsto ωcan atTop (𝓝 0) ∧
    ∀ n ≥ N, ∀ B, IsBclass a (ν n) B →
      |((S n).IT (fun s => if ν n ^ (-(3 / 2 : ℝ)) ≤ s then
            (S n).Mcell s ((S n).xi (μ : ℂ) B s) else fun _ => 0)) -
          (3 * Real.pi / (2 * (S n).c)) * (μ + 3 / 2) * ν n ^ (3 + 2 * μ) *
            (((S n).aNuC lam κ μ (ν n) B) * Nnu lam κ (ν n) * J (μ : ℂ)).im| ≤
        C * ((‖Nnu lam κ (ν n)‖ * ν n ^ (3 + 2 * μ) / (S n).c) * (ν n + ωcan n)) * bNorm a B

/-- Flat all-moments (4637-4640), concrete: from the old-output moment bound (young later output
4421-4439) via the absolute stress impulse; the input is `FlatMomentInput`. -/
def FlatMomentInput (S : ℕ → FlatSetting) (ν : ℕ → ℝ) (lam κ : ℂ) (μ a : ℝ) : Prop :=
  FlatAllMoments (fun n => (S n).toPkg lam κ (ν n) μ) ν lam κ μ a

/-! ## Remaining flat inputs and conditionals (source 4570-4732) -/

/-- Cutoff profile `χ̂_f` (source 4572-4573): `C¹` with continuous derivative, `= 1` on `(-∞,1]`
(in particular on `[0,1]`) and `= 0` on `[1.1,∞)`. -/
structure FlatCutoffProfile (chi dchi : ℝ → ℝ) : Prop where
  deriv : ∀ x, HasDerivAt chi (dchi x) x
  dchi_cont : Continuous dchi
  one_le : ∀ x, x ≤ 1 → chi x = 1
  zero_ge : ∀ x, 1.1 ≤ x → chi x = 0

/-- Standing hypotheses of the flat-return section (source 4557-4592): the young
hypotheses with `Σ = 2`, `α = 1.1` (`T_f = 1.1/ν`, `H = 2/ν`), the laws of every young package,
`c = ν⁻²` (4557, 4343; used as "use `c⁻¹ = ν²`", 4724), `ε³ > 0`, the old cutoff `χ_o` (0 for
`s ≤ 1.2/ν`, 1 for `s ≥ 1.5/ν`, 4573-4574), `0 < μ` (`μ ∈ K ⋐ (0,1/4)`, 4557),
`0 < a < γ/16` (4586) with `γ = Re λ`, and uniform bounds of the periodized Gaussian sources
`H_{t,c}`, `R_{t,c}` on the support of the forcing.

Regularity in the age (needed because `a_{ν,+}`, `ξ_B`, `I_T` are Bochner integrals in `t`/`s`):
the sources `H_{t,c}`, `R_{t,c}` are periodizations of the explicit Gaussian profiles of
4565-4569, smooth in `t` (`a(t) = 1 + νt`), hence strongly measurable; the frozen-pair pairings
`t ↦ ℓ_{+,νt,c} H_{t,c}`, `ℓ_{+,νt,c} H̄_{t,c}`, `ℓ_{+,νt,c} R_{t,c}` entering the explicit
amplitude `a_{ν,+}(B) = ∫₀^{1.1/ν} t^μ F_+(t,0)⁻¹ ℓ_{+,νt,c} g_B(t) dt` (4645-4648) are
continuous in `t` (heat-scaled pair, 4352-4356, 4650-4654), hence measurable; the old cutoff
`χ_o` is a fixed smooth cutoff (4573), hence measurable. -/
structure FlatSettingHyp (S : ℕ → FlatSetting) (ν : ℕ → ℝ) (lam : ℂ) (μ a : ℝ) : Prop where
  young : YoungHyp ν lam 2 1.1
  laws : ∀ n, YoungLaws (S n).pk (S n).conjX
  c_eq : ∀ n, (S n).c = (ν n)⁻¹ ^ 2
  eps3_pos : ∀ n, 0 < (S n).eps3
  chiO_zero : ∀ n s, s ≤ 1.2 / ν n → (S n).chiO s = 0
  chiO_one : ∀ n s, 1.5 / ν n ≤ s → (S n).chiO s = 1
  mu_pos : 0 < μ
  a_pos : 0 < a
  a_lt : a < lam.re / 16
  src_bdd : ∃ C : ℝ, ∀ n, ∀ t ∈ Icc (0 : ℝ) (1.1 / ν n),
    ‖(S n).Hper t‖ ≤ C ∧ ‖(S n).conjX ((S n).Hper t)‖ ≤ C ∧ ‖(S n).Rper t‖ ≤ C
  src_meas : ∀ n, StronglyMeasurable (S n).Hper ∧ StronglyMeasurable (S n).Rper
  pair_meas : ∀ n, Measurable (fun t => (S n).pk.ell true t ((S n).Hper t)) ∧
    Measurable (fun t => (S n).pk.ell true t ((S n).conjX ((S n).Hper t))) ∧
    Measurable (fun t => (S n).pk.ell true t ((S n).Rper t))
  chiO_meas : ∀ n, Measurable (S n).chiO

/-- Flat class amplitude (source 4624-4626, proof 4643-4661), concrete:
`|a_{ν,+}(B) - a₀(B)| ≤ C ν ‖B‖_a` uniformly on `𝓑_a`, from the standing hypotheses (in
particular `c = ν⁻²`, so the Gaussian comparison error `O(νt + c⁻²)` is `O(νt + ν⁴)`,
`0 < a < γ/16`, `0 < μ`, and the measurability of the pairings `ℓ_{+,νt,c} H_{t,c}`, ...)
and the direct/dual Gaussian comparison (4650-4654). -/
def FlatClassAmplitudeC (S : ℕ → FlatSetting) (ν : ℕ → ℝ) (lam κ ell : ℂ) (μ a : ℝ) : Prop :=
  FlatSettingHyp S ν lam μ a → FlatGaussComparison S ν ell →
    FlatClassAmplitude (fun n => (S n).toPkg lam κ (ν n) μ) ν lam ell (μ : ℂ) a

/-- The integrand of `I_T` (source 4584-4587). -/
def FlatSetting.ITdens (S : FlatSetting) (M : ℝ → ℝ × ℝ → Matrix (Fin 3) (Fin 3) ℝ) (s : ℝ) : ℝ :=
  S.chiO s * s ^ (-(3 / 2 : ℝ)) * cellInt S.c (fun p => 2 * M s p 2 2 - M s p 0 0)

theorem FlatSetting.IT_eq (S : FlatSetting) (M : ℝ → ℝ × ℝ → Matrix (Fin 3) (Fin 3) ℝ) :
    S.IT M = ∫ s in Ioi (0 : ℝ), S.ITdens M s := rfl

/-- Integrability of the two pieces (`s ≥ u_o` and `s < u_o`, `u_o = ν^{-3/2}`) of the `I_T`
integrand of the tested stress `M_B`, `B ∈ 𝓑_a` (needed to split `I_T`; source 4672-4690). -/
def FlatITIntegrable (S : ℕ → FlatSetting) (ν : ℕ → ℝ) (μ a : ℝ) : Prop :=
  ∀ n, ∀ B, IsBclass a (ν n) B →
    Integrable (fun s => (S n).ITdens (fun s => if ν n ^ (-(3 / 2 : ℝ)) ≤ s then
        (S n).Mcell s ((S n).xi (μ : ℂ) B s) else fun _ => 0) s) (volume.restrict (Ioi (0 : ℝ))) ∧
    Integrable (fun s => (S n).ITdens (fun s => if s < ν n ^ (-(3 / 2 : ℝ)) then
        (S n).Mcell s ((S n).xi (μ : ℂ) B s) else fun _ => 0) s) (volume.restrict (Ioi (0 : ℝ)))

/-- Earlier-old part (source 4686-4688): for every `0 < γ' < Re λ`,
`|I_T(M_B; s < u_o)| ≤ C 𝒜_ν P_ν e^{-γ'/√ν} ‖B‖_a`, `𝒜_ν = |N_ν| ν^{3+2μ}/c`
("by the full forward gain estimate"), `P_ν = ν^{-k}`. -/
def FlatEarlierOld (S : ℕ → FlatSetting) (ν : ℕ → ℝ) (lam κ : ℂ) (μ a : ℝ) : Prop :=
  ∀ γ' : ℝ, 0 < γ' → γ' < lam.re →
    ∃ (C : ℝ) (k : ℕ) (N : ℕ), ∀ n ≥ N, ∀ B, IsBclass a (ν n) B →
      |(S n).IT (fun s => if s < ν n ^ (-(3 / 2 : ℝ)) then
            (S n).Mcell s ((S n).xi (μ : ℂ) B s) else fun _ => 0)| ≤
        C * (‖Nnu lam κ (ν n)‖ * ν n ^ (3 + 2 * μ) / (S n).c) *
          ((ν n)⁻¹ ^ k * Real.exp (-γ' / Real.sqrt (ν n))) * bNorm a B

/-- Conditional scalar estimate (source 4628-4632, proof 4662-4690): `FlatScalarEstimate` for the
concrete packages from the class amplitude (4624), the old anisotropy law (4669-4672), the
earlier-old bound (4686) and integrability of the `I_T` pieces.
Proof sketch: `I_T = I_T(s ≥ u_o) + I_T(s < u_o)` (pointwise split of the integrand, `integral_add`),
`ℓ_μ = ε³ I_T/(8(μ+3/2))`, `c = ν⁻²`, `Im z = -Re(i z)`, and
`|a_{ν,+} - a_0| ≤ Cν‖B‖_a` in the amplitude term (`η_ν := ν`). -/
def FlatScalarEstimateC (S : ℕ → FlatSetting) (ν : ℕ → ℝ) (lam κ ell : ℂ) (J : ℂ → ℂ)
    (μ a : ℝ) : Prop :=
  FlatSettingHyp S ν lam μ a →
  FlatClassAmplitude (fun n => (S n).toPkg lam κ (ν n) μ) ν lam ell (μ : ℂ) a →
  FlatOldAnisotropy S ν lam κ J μ a → FlatEarlierOld S ν lam κ μ a → FlatITIntegrable S ν μ a →
    FlatScalarEstimate (fun n => (S n).toPkg lam κ (ν n) μ) ν (fun n => (S n).eps3)
      lam κ ell J μ a

/-- Tested source norm bound (source 4665-4667): `‖g_B‖_{𝓘_{ν,μ}} ≤ C ‖B‖_a` for `α = 1.1`. -/
def FlatTestedSourceNorm (S : ℕ → FlatSetting) (ν : ℕ → ℝ) (lam κ : ℂ) (μ a : ℝ) : Prop :=
  ∃ (C : ℝ) (N : ℕ), ∀ n ≥ N, ∀ B, IsBclass a (ν n) B →
    testedNorm (S n).pk lam κ (ν n) (μ : ℂ) (1.1 / ν n) ((S n).gB B) ≤ C * bNorm a B

/-- State at `H = 2/ν` of the Duhamel solution (young source theorem, source 4490-4496, with the
bare columns bounded by `|F_+(H,0)|` by the frozen pair, 4407-4412):
`‖H^μ ξ_B(H)‖ ≤ C |F_+(H,0)| ‖g_B‖_𝓘`. -/
def FlatStateAtH (S : ℕ → FlatSetting) (ν : ℕ → ℝ) (lam κ : ℂ) (μ a : ℝ) : Prop :=
  ∃ (C : ℝ) (N : ℕ), ∀ n ≥ N, ∀ B, IsBclass a (ν n) B →
    ‖duhamel (S n).pk (μ : ℂ) ((S n).gB B) (2 / ν n)‖ ≤
      C * ‖Fpm true lam κ (ν n) (2 / ν n) 0‖ *
        testedNorm (S n).pk lam κ (ν n) (μ : ℂ) (1.1 / ν n) ((S n).gB B)

/-- Young later output (source 4421-4439, eq `eq:young-later-output`, 4660-4668, 4687-4693):
every old weighted moment and absolute stress functional has norm at most
`C |F_+(H,0)|⁻¹ ‖w(H)‖` after division by its canonical scale `|N_ν| ν^{3+2μ}/c`, with the extra
factor `ν^k` for `k = 0, 1` ("`s^{-k/2} = ν^k θ^{k/2}(1-νθ)^{-k/2}`"). -/
def FlatLaterOutput (S : ℕ → FlatSetting) (ν : ℕ → ℝ) (lam κ : ℂ) (μ a : ℝ) : Prop :=
  ∃ (C : ℝ) (N : ℕ), ∀ n ≥ N, ∀ k : ℕ, k ≤ 1 → ∀ B, IsBclass a (ν n) B →
    (S n).momentC lam κ μ k B ≤
      C * (‖Nnu lam κ (ν n)‖ * ν n ^ (3 + 2 * μ) / (S n).c) * ν n ^ k *
        (‖Fpm true lam κ (ν n) (2 / ν n) 0‖⁻¹ * ‖duhamel (S n).pk (μ : ℂ) ((S n).gB B) (2 / ν n)‖)

/-- Conditional all-moments (source 4637-4640, proof 4686-4693): `FlatAllMoments` from
the tested source norm, the state bound and the later-output bound.
Sketch: `‖F_+(H,0)‖ ≠ 0` (`F = exp(·)·(3)^κ`, `a(H)/a(0) = 3`), cancel, then `c = ν⁻²` gives
`ν^{3+2μ}/c = ν^{5+2μ}`. -/
def FlatAllMomentsC (S : ℕ → FlatSetting) (ν : ℕ → ℝ) (lam κ : ℂ) (μ a : ℝ) : Prop :=
  FlatSettingHyp S ν lam μ a → FlatTestedSourceNorm S ν lam κ μ a → FlatStateAtH S ν lam κ μ a →
  FlatLaterOutput S ν lam κ μ a →
    FlatAllMoments (fun n => (S n).toPkg lam κ (ν n) μ) ν lam κ μ a

/-- Explicit Laplace integral (source 4709-4715), for the unit source `B_μ`:
`a_0(B_μ) = -(21/4) L(μ) + O(P_ν e^{-b/ν})` (proved for all `0 < ν ≤ ν₀` as `a0Unit`,
`Proofs/A0Unit.lean`). -/
def FlatLaplace (ν : ℕ → ℝ) (lam ell : ℂ) (chi dchi : ℝ → ℝ) (μ : ℝ) : Prop :=
  ∃ (C b : ℝ) (k : ℕ) (N : ℕ), 0 < b ∧ ∀ n ≥ N,
    ‖aZero lam ell (μ : ℂ) (Bmu chi dchi (ν n) μ) + (21 / 4 : ℂ) * LCoeff lam ell (μ : ℂ)‖ ≤
      C * (ν n)⁻¹ ^ k * Real.exp (-b / ν n)

/-- The unit source `B_μ` lies in `𝓑_a` with bounded norm (source 4697-4709: `B_μ = r_μ D₀` with
`D₀` trace-free diagonal, `r_μ(s) = 0` for `s ≤ 0` and `s ≥ 1.1/ν`, `|B_μ| ≤ C s^{3/2}` on the
support). -/
def FlatUnitInClass (ν : ℕ → ℝ) (chi dchi : ℝ → ℝ) (μ a : ℝ) : Prop :=
  ∃ C : ℝ, ∀ n, IsBclass a (ν n) (Bmu chi dchi (ν n) μ) ∧ bNorm a (Bmu chi dchi (ν n) μ) ≤ C

/-- Conditional coefficient corollary (source 4697-4732): `FlatCoefficient` from the scalar estimate
(applied to `B_μ` with a fixed `γ'`), the Laplace integral and the unit-class membership.
Sketch: substitute `a_0(B_μ) = -(21/4)L + e` in `Re[i a_0 N J]`;
`(3π/16)(21/4) = 2 · 63π/128`, so the main term equals `unitResp`; the remainder is
`(3π/16) ε³ ν^{5+2μ}|N||J(μ)||e|` ≤ `C A_* ν^{-k} e^{-b/ν}`. -/
def FlatCoefficientC (S : ℕ → FlatSetting) (ν : ℕ → ℝ) (lam κ ell : ℂ) (J : ℂ → ℂ)
    (chi dchi : ℝ → ℝ) (μ a : ℝ) : Prop :=
  FlatSettingHyp S ν lam μ a → FlatCutoffProfile chi dchi →
  FlatScalarEstimate (fun n => (S n).toPkg lam κ (ν n) μ) ν (fun n => (S n).eps3) lam κ ell J μ a →
  FlatLaplace ν lam ell chi dchi μ → FlatUnitInClass ν chi dchi μ a →
    FlatCoefficient (fun n => (S n).toPkg lam κ (ν n) μ) ν (fun n => (S n).eps3) lam κ ell J
      chi dchi μ

end ConcreteYF

end UnforcedLeray.Short.PartIIIb

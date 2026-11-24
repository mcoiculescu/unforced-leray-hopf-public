import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9

/-!
# `PartII-a:N01/9/1` (decomposition): `BodyColumnEnergyC`

Source of record `the November 2 reference manuscript`
lines 1650-1658 (`A₀`), 1669-1674 (`T₀ = (μ - A₀)⁻¹P₀`), 1684-1689 (pair the flat equation with
`s^{-1/2} b̄`: `(Re μ + 1/4)‖b‖²_𝓗 + ν‖∇b‖²_𝒯 ≤ ‖h‖_𝓗‖b‖_𝓗`), 3426-3430 (energy class closed under
`L²` limits, null-set redefinition), 3541-3552 (energy identity).

The energy statement holds for every `G ∈ 𝓗` (the hypothesis `G = s div₀ M` is not used), because
`T0flat G = R₀(μ)(P₀ G)`.  Route: smooth periodic forces `SmoothForceSet` are dense in `𝓗`
(`SmoothForceDense`); for them `R₀(μ)g` is classical (`B0225.R0_Ms_ae`) and lies in the energy
class (`SmoothForceFields`); the energy inequality gives a bound on the difference of gradients
(`SmoothForceGradBound`); `EnergyClosure` passes to the `𝓗`-limit.  `bodyColumnEnergyC_of` is the
(proved) assembly.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.N01

open UnforcedLeray.B0220 (Profile HSpace measureH)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.Short.PartIIIb.Concrete (Chart)
open UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst (IsEnergyFieldAE)
open UnforcedLeray.Short.PartIIIb.NearInst.Delta (velF)
open UnforcedLeray.Short.IIIa (tnorm2)

/-- A smooth force: `C^∞` meridional field on the profile space, `c`-periodic in `q`, supported in
`s ∈ [s₁, s₂] ⊂ (0,∞)` and `|η| ≤ R` (source 1684-1689: "smooth compactly supported forces"). -/
def IsSmoothForceFn (c : ℝ) (F : Profile → MeridC) : Prop :=
  ContDiff ℝ ∞ F ∧ (∀ p : Profile, F (p.1, p.2.1 + c, p.2.2) = F p) ∧
    ∃ s₁ s₂ R : ℝ, 0 < s₁ ∧ ∀ p : Profile, (p.1 < s₁ ∨ s₂ < p.1 ∨ R < |p.2.2|) → F p = 0

/-- The solenoidal elements of `𝓗` (`g ∈ solenoidalHC 0 c`) represented by smooth forces; then
`R₀(μ)g = T₀ g` is divergence free, as the energy class requires. -/
def SmoothForceSet (c : ℝ) : Set (HSpace c MeridC) :=
  {g | g ∈ solenoidalHC 0 c ∧ ∃ F, IsSmoothForceFn c F ∧ (g : Profile → MeridC) =ᵐ[measureH c] F}

/-- **Leaf (a)**: smooth periodic solenoidal forces are dense in the solenoidal subspace
`solenoidalHC 0 c` of `𝓗 = L²(s^{-3/2}; L²(cell))` (e.g. project smooth forces with the flat Leray
projection, a Fourier multiplier in `(q,η)` for each `s`). -/
def SmoothForceDense : Prop :=
  ∀ c : ℝ, 0 < c → ∀ g ∈ solenoidalHC 0 c, g ∈ closure (SmoothForceSet c)

/-- **Leaf (b)**: for a smooth force `g`, `R₀(μ)g` has a representative in the energy class
(`B0225.R0_Ms_ae`: `R₀(μ)M_s g(s) = ∫₀^s (σ/s)^μ e^{ν(s-σ)Δ} g(σ)dσ`, classical for smooth `g`;
`divFree`, `weakGrad` hold for all ages; `zeroEntrance` from `R₀ g ∈ 𝓗`). -/
def SmoothForceFields : Prop :=
  ∀ (c ν : ℝ) (hc : 0 < c), 0 < ν → ∀ μ : ℂ, 0 < μ.re + 1 / 4 →
    ∀ g ∈ SmoothForceSet c, ∃ (b : Chart → Fin 2 → ℂ) (Gr : Chart → Fin 2 → Fin 2 → ℂ),
      b =ᵐ[ageμ c (-3 / 2)] velF c (UnforcedLeray.B0225.R0 hc ν μ g : HSpace c MeridC) ∧
        IsEnergyFieldAE c b Gr

/-- **Leaf (c), the energy inequality** (1684-1689: pairing with `s^{-1/2} b̄`,
`(Re μ + 1/4)‖b‖²_𝓗 + ν‖∇b‖²_𝒯 ≤ ‖h‖_𝓗‖b‖_𝓗 ≤ (Re μ+1/4)⁻¹‖h‖²_𝓗`, applied to the difference of
two smooth forces; the weak gradient of an energy field is unique a.e.).  `C` depends on `c, ν, μ`
only (the `𝓗` norm uses the unnormalised cell measure, `ageμ` the normalised one). -/
def SmoothForceGradBound : Prop :=
  ∀ (c ν : ℝ) (hc : 0 < c), 0 < ν → ∀ μ : ℂ, 0 < μ.re + 1 / 4 →
    ∃ C : ℝ, ∀ g₁ ∈ SmoothForceSet c, ∀ g₂ ∈ SmoothForceSet c,
      ∀ (b₁ b₂ : Chart → Fin 2 → ℂ) (G₁ G₂ : Chart → Fin 2 → Fin 2 → ℂ),
        b₁ =ᵐ[ageμ c (-3 / 2)] velF c (UnforcedLeray.B0225.R0 hc ν μ g₁ : HSpace c MeridC) →
        IsEnergyFieldAE c b₁ G₁ →
        b₂ =ᵐ[ageμ c (-3 / 2)] velF c (UnforcedLeray.B0225.R0 hc ν μ g₂ : HSpace c MeridC) →
        IsEnergyFieldAE c b₂ G₂ →
        ∫⁻ p, ENNReal.ofReal (tnorm2 (fun i j => G₁ p i j - G₂ p i j) ^ 2) ∂(ageμ c (-1 / 2))
          ≤ ENNReal.ofReal (C * ‖g₁ - g₂‖ ^ 2)

/-- **Leaf (d), closure of the energy class** (3426-3430): if `g_k → g` in `𝓗`, `(b_k, G_k)` are
energy fields with `b_k = R₀(μ)g_k` a.e. and `(G_k)` is Cauchy in `L²(s^{-1/2})`, then `R₀(μ)g`
has an energy-class representative (`b_k → b` in `L²(s^{-3/2})` by `‖R₀‖ ≤ (Re μ+1/4)⁻¹`; the
limit gradient and an a.e. subsequence give `divFreeAE`, `weakGradAE`; `zeroEntrance` from
`b ∈ 𝓗`; `energyLoc` from the two `L²` limits). -/
def EnergyClosure : Prop :=
  ∀ (c ν : ℝ) (hc : 0 < c), 0 < ν → ∀ μ : ℂ, 0 < μ.re + 1 / 4 →
    ∀ (g : HSpace c MeridC) (gk : ℕ → HSpace c MeridC), Tendsto gk atTop (𝓝 g) →
      ∀ (bk : ℕ → Chart → Fin 2 → ℂ) (Gk : ℕ → Chart → Fin 2 → Fin 2 → ℂ),
        (∀ k, bk k =ᵐ[ageμ c (-3 / 2)] velF c (UnforcedLeray.B0225.R0 hc ν μ (gk k) : HSpace c MeridC) ∧
          IsEnergyFieldAE c (bk k) (Gk k)) →
        (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ k ≥ N, ∀ l ≥ N,
          ∫⁻ p, ENNReal.ofReal (tnorm2 (fun i j => Gk k p i j - Gk l p i j) ^ 2)
            ∂(ageμ c (-1 / 2)) < ENNReal.ofReal ε) →
        ∃ (b : Chart → Fin 2 → ℂ) (Gr : Chart → Fin 2 → Fin 2 → ℂ),
          b =ᵐ[ageμ c (-3 / 2)] velF c (UnforcedLeray.B0225.R0 hc ν μ g : HSpace c MeridC) ∧
            IsEnergyFieldAE c b Gr

theorem bodyColumnEnergyC_of (h1 : SmoothForceDense) (h2 : SmoothForceFields)
    (h3 : SmoothForceGradBound) (h4 : EnergyClosure) : BodyColumnEnergyC := by
  intro c ν hc hν μ hμ M _ G _
  set g : HSpace c MeridC := PepsC 0 c G with hg
  have hT : T0flat hc ν μ G = UnforcedLeray.B0225.R0 hc ν μ g := rfl
  rw [hT]
  have hgs : g ∈ solenoidalHC 0 c := Submodule.starProjection_apply_mem _ _
  have hD := h1 c hc g hgs
  have hex : ∀ k : ℕ, ∃ y ∈ SmoothForceSet c, dist g y < 1 / ((k : ℝ) + 1) := fun k =>
    Metric.mem_closure_iff.1 hD _ (by positivity)
  choose gk hgk hdist using hex
  have hlim : Tendsto gk atTop (𝓝 g) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    refine squeeze_zero (fun k => dist_nonneg) (fun k => ?_) this
    rw [dist_comm]; exact (hdist k).le
  have hfld := fun k => h2 c ν hc hν μ hμ (gk k) (hgk k)
  choose bk Gk hbk hEk using hfld
  obtain ⟨C, hC⟩ := h3 c ν hc hν μ hμ
  refine h4 c ν hc hν μ hμ g gk hlim bk Gk (fun k => ⟨hbk k, hEk k⟩) ?_
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (4 * (|C| + 1) / ε)
  refine ⟨N, fun k hk l hl => ?_⟩
  refine lt_of_le_of_lt (hC (gk k) (hgk k) (gk l) (hgk l) _ _ _ _ (hbk k) (hEk k) (hbk l) (hEk l))
    ((ENNReal.ofReal_lt_ofReal_iff hε).2 ?_)
  have hk1 : 1 / ((k : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
    apply one_div_le_one_div_of_le (by positivity)
    have : (N : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hl1 : 1 / ((l : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
    apply one_div_le_one_div_of_le (by positivity)
    have : (N : ℝ) ≤ l := by exact_mod_cast hl
    linarith
  have hnorm : ‖gk k - gk l‖ ≤ 2 / ((N : ℝ) + 1) := by
    have h1' := hdist k
    have h2' := hdist l
    have : ‖gk k - gk l‖ ≤ dist g (gk k) + dist g (gk l) := by
      calc ‖gk k - gk l‖ = dist (gk k) (gk l) := (dist_eq_norm _ _).symm
        _ ≤ dist (gk k) g + dist g (gk l) := dist_triangle _ _ _
        _ = _ := by rw [dist_comm (gk k) g]
    have : dist g (gk k) + dist g (gk l) ≤ 2 / ((N : ℝ) + 1) := by
      have e2 : 2 / ((N : ℝ) + 1) = 1 / ((N : ℝ) + 1) + 1 / ((N : ℝ) + 1) := by ring
      have := hdist k; have := hdist l; linarith
    linarith
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hq : ‖gk k - gk l‖ ^ 2 ≤ 4 / ((N : ℝ) + 1) := by
    have h0 : 0 ≤ ‖gk k - gk l‖ := norm_nonneg _
    have hle : ‖gk k - gk l‖ ^ 2 ≤ (2 / ((N : ℝ) + 1)) ^ 2 := pow_le_pow_left₀ h0 hnorm 2
    have hN1' : (1 : ℝ) ≤ (N : ℝ) + 1 := by have : (0:ℝ) ≤ N := Nat.cast_nonneg N; linarith
    calc ‖gk k - gk l‖ ^ 2 ≤ (2 / ((N : ℝ) + 1)) ^ 2 := hle
      _ = 4 / ((N : ℝ) + 1) ^ 2 := by field_simp; norm_num
      _ ≤ 4 / ((N : ℝ) + 1) := by
        apply div_le_div_of_nonneg_left (by norm_num) hN1
        nlinarith
  have hsq : 0 ≤ ‖gk k - gk l‖ ^ 2 := by positivity
  have hcN : ε * ((N : ℝ) + 1) > 4 * (|C| + 1) := by
    have := (div_lt_iff₀ hε).1 hN
    nlinarith
  calc C * ‖gk k - gk l‖ ^ 2 ≤ |C| * ‖gk k - gk l‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (le_abs_self C) hsq
    _ ≤ |C| * (4 / ((N : ℝ) + 1)) := mul_le_mul_of_nonneg_left hq (abs_nonneg C)
    _ < ε := by
        rw [← mul_div_assoc, div_lt_iff₀ hN1]
        nlinarith [abs_nonneg C]

end UnforcedLeray.Short.PartIIa.N01

import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org3

/-!
# Part III-a, `PartIII-a:T21/c3/2/1/1/org/3/b`: the planar limit interaction (SP 2920-2927, 2972-2980)

Source: `the November 2 reference manuscript` (SP) 2898-2935, 2972-2980.

## The planar limit `A0`

`A_rel(τ)` is the cell zero extension of `movLInt + movFrameRankPert`
(`eq:short-causal-damped-complement`: `𝓑 = G - β₀ - E H₀ + [-K₀ + (β₀ - 1)E + E M₀] Λ`,
SP 2920-2923). In the successive limit (`d(r) → ∞`, `θ ≥ b → ∞`, `ν → 0`):
`movLInt → 𝒜 = couplingW` (the planar Biot–Savart coupling, `𝓛 = T + 𝒜`, `eulerGroupW` is the
Dyson evolution of `(T, 𝒜)`), `E_i → e_i = κ.e i`, `Λ_i → ℓ_i = ∫ κ.lamP i ·`,
`H₀ W → ℓ(𝓛W) = λ_i ℓ_i(W)`, `K₀ → 𝓛 e_j = λ_j e_j`, `M₀ → diag λ_j`, `β₀ → γ = Re λ`
(`λ₀ = λ`, `λ₁ = λ̄` the seed pair). Hence (SP 2926-2927)
`A0 = 𝒜 - 𝒫𝓛𝒫 + (γ - 1)𝒫`, `𝒫 W = Σ_i ℓ_i(W) e_i`, i.e.
`A0 W = 𝒜 W + Σ_i (γ - 1 - λ_i) ℓ_i(W) e_i` (`IsPlanarDampedInt`; the eigenvalue is the one of
the seed data of `κ`, which makes the statement independent of `λ = P.eigenvalue`).
Its relative Dyson evolution is `e^{-γt}(e^{t𝓛}𝒬 + e^{(γ-1)t}𝒫) = e^{-γt}e^{t𝓛}𝒬 + e^{-t}𝒫`, whose norm
is at most `C₀e^{-hB} + Cproj e^{-B}` by `SeedCtx` (`𝒬` part, zero-mass data; the radial mass
direction `⟨y⟩^{-2m}` is annihilated by `𝓛` and `𝒫`, is orthogonal to the zero-mass subspace, and
decays at rate `γ ≥ h` with `C₀ ≥ 1` from `SeedCtx` at `t = 0`) and `SeedProjBdd` (`𝒫` part).

## Leaves (Prop, exact statements below) and the proved assembly

* `PlanarDampedIntExists` (SP 2920-2925): the bounded extension `A0` exists.
* `PlanarDampedIntCompact` (SP 2972-2974: source and observation truncation, local Rellich
  compactness; finite-rank part): `A0` is compact.
* `PlanarDampedDysonBound` (SP 2926-2935, 2976-2980): the Dyson sum of
  `(planarRelTransportRe, A0)` obeys `‖U0 B 0‖ ≤ C₀ e^{-hB} + Cproj e^{-B}`.
* Proved here: `dysonDefined_planarRelTransportRe` (the Dyson iteration of
  `(planarRelTransportRe, A)` is defined for every constant bounded `A`: iterates are continuous,
  via the factorization `e^{-γ(t-s)}T(t-s) = e^{-γt}T(t) ∘ e^{γs}T(-s)` and joint continuity of
  the transport group).
* `PlanarDampedIntLimit` (SP 2898-2925, 2974-2978: image and dual estimates):
  `‖A_rel r - A0‖ → 0` in the successive limit, uniformly in train, entrance time, `r ∈ [0,B]`.
* `relPlanarInteraction_of`: the four leaves give `RelPlanarInteraction κ` (constant `A0`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric UnforcedLeray.Blueprint.Planar

namespace UnforcedLeray.Short.IIIa

open FrameShortBlockSub FrameBlockContractSub CompactDuhamelGapSub

namespace BlockPropagatorInteriorSub

open OrgSplit
open scoped ComplexConjugate ContDiff InnerProductSpace InnerProduct ENNReal

namespace OrgSplit3

namespace PlanarB

/-! ## The Dyson iteration of `(planarRelTransportRe, A0)` is defined (proved) -/

/-- Joint continuity of the transport group: `(a, v) ↦ T(a) v`. -/
theorem continuous_transportGroupW_joint (M : ℝ) :
    Continuous fun p : ℝ × Planar.L2w M => Planar.transportGroupW M p.1 p.2 := by
  rw [continuous_iff_continuousAt]
  rintro ⟨a₀, v₀⟩
  have h1 : Tendsto (fun p : ℝ × Planar.L2w M => Planar.transportGroupW M p.1 (p.2 - v₀))
      (𝓝 (a₀, v₀)) (𝓝 0) := by
    refine squeeze_zero_norm (a := fun p : ℝ × Planar.L2w M => ‖p.2 - v₀‖) (fun p => ?_) ?_
    · calc ‖Planar.transportGroupW M p.1 (p.2 - v₀)‖
          ≤ ‖Planar.transportGroupW M p.1‖ * ‖p.2 - v₀‖ := (Planar.transportGroupW M p.1).le_opNorm _
        _ ≤ 1 * ‖p.2 - v₀‖ :=
            mul_le_mul_of_nonneg_right (Planar.norm_transportGroupW_le M p.1) (norm_nonneg _)
        _ = ‖p.2 - v₀‖ := one_mul _
    · have : Tendsto (fun p : ℝ × Planar.L2w M => p.2 - v₀) (𝓝 (a₀, v₀)) (𝓝 (v₀ - v₀)) :=
        (continuous_snd.sub continuous_const).tendsto _
      rw [sub_self] at this
      exact tendsto_norm_zero.comp this
  have h2 : Tendsto (fun p : ℝ × Planar.L2w M => Planar.transportGroupW M p.1 v₀)
      (𝓝 (a₀, v₀)) (𝓝 (Planar.transportGroupW M a₀ v₀)) :=
    ((Planar.continuous_transportGroupW_apply M v₀).comp continuous_fst).tendsto (a₀, v₀)
  have h3 := h1.add h2
  rw [zero_add] at h3
  refine h3.congr fun p => ?_
  simp only [map_sub, sub_add_cancel]

/-- Continuity of `x ↦ e^{c a(x)} T(k a(x)) v(x)` for continuous `a`, `v`. -/
theorem continuous_expSmulTransport {X : Type*} [TopologicalSpace X] (M c k : ℝ) {a : X → ℝ}
    {v : X → Planar.L2w M} (ha : Continuous a) (hv : Continuous v) :
    Continuous fun x => ((Real.exp (c * a x) : ℝ) : ℂ) • Planar.transportGroupW M (k * a x) (v x) := by
  have h1 : Continuous fun x => ((Real.exp (c * a x) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul ha))
  have h2 : Continuous fun x => ((k * a x, v x) : ℝ × Planar.L2w M) :=
    (continuous_const.mul ha).prodMk hv
  have h3 := (continuous_transportGroupW_joint M).comp h2
  simp only [Function.comp_def] at h3
  exact h1.smul h3

theorem continuous_clampB (B : ℝ) : Continuous (clampB B) := by
  unfold clampB
  exact continuous_const.max (continuous_id.min continuous_const)

/-- Factorization `e^{-γ(t-s)}T(t-s) = (e^{-γt}T(t)) ∘ (e^{γs}T(-s))`. -/
theorem planarRelTransportRe_apply_eq (P : PlanarData) (m t s : ℝ) (x : Planar.L2w m) :
    planarRelTransportRe P m t s x =
      ((Real.exp (-P.eigenvalue.re * t) : ℝ) : ℂ) • Planar.transportGroupW m (1 * t)
        (((Real.exp (P.eigenvalue.re * s) : ℝ) : ℂ) • Planar.transportGroupW m (-1 * s) x) := by
  unfold planarRelTransportRe
  rw [map_smul, smul_smul, smul_apply, ← ContinuousLinearMap.comp_apply,
    ← Planar.transportGroupW_add]
  congr 2
  · rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  · ring

theorem dysonTerm_succ_planarRelTransportRe (P : PlanarData) (m B : ℝ)
    (A0 : Planar.L2w m →L[ℂ] Planar.L2w m) (k : ℕ) (t s : ℝ) (x : Planar.L2w m) :
    UnforcedLeray.B0104.dysonTerm (ι := Unit)
        (fun _ => fun τ σ => planarRelTransportRe P m (clampB B τ) (clampB B σ))
        (fun _ _ => A0) (k + 1) () t s x =
      ∫ r in s..t, planarRelTransportRe P m (clampB B t) (clampB B r)
        (A0 (UnforcedLeray.B0104.dysonTerm (ι := Unit)
          (fun _ => fun τ σ => planarRelTransportRe P m (clampB B τ) (clampB B σ))
          (fun _ _ => A0) k () r s x)) := rfl

/-- The Dyson iterates of `(planarRelTransportRe, A0)` are continuous in the exit time. -/
theorem continuous_dysonTerm_planarRelTransportRe (P : PlanarData) (m B : ℝ)
    (A0 : Planar.L2w m →L[ℂ] Planar.L2w m) (k : ℕ) (s : ℝ) (x : Planar.L2w m) :
    Continuous fun t => UnforcedLeray.B0104.dysonTerm (ι := Unit)
      (fun _ => fun τ σ => planarRelTransportRe P m (clampB B τ) (clampB B σ))
      (fun _ _ => A0) k () t s x := by
  set γ := P.eigenvalue.re
  have hc := continuous_clampB B
  induction k with
  | zero =>
    show Continuous fun t => planarRelTransportRe P m (clampB B t) (clampB B s) x
    simp_rw [planarRelTransportRe_apply_eq]
    exact continuous_expSmulTransport m (-γ) 1 hc continuous_const
  | succ k ih =>
    set V := fun r => UnforcedLeray.B0104.dysonTerm (ι := Unit)
      (fun _ => fun τ σ => planarRelTransportRe P m (clampB B τ) (clampB B σ))
      (fun _ _ => A0) k () r s x
    have hφ : Continuous fun r => ((Real.exp (γ * clampB B r) : ℝ) : ℂ) •
        Planar.transportGroupW m (-1 * clampB B r) (A0 (V r)) :=
      continuous_expSmulTransport m γ (-1) hc (A0.continuous.comp ih)
    have heq : ∀ t, UnforcedLeray.B0104.dysonTerm (ι := Unit)
        (fun _ => fun τ σ => planarRelTransportRe P m (clampB B τ) (clampB B σ))
        (fun _ _ => A0) (k + 1) () t s x =
        ((Real.exp (-γ * clampB B t) : ℝ) : ℂ) • Planar.transportGroupW m (1 * clampB B t)
          (∫ r in s..t, ((Real.exp (γ * clampB B r) : ℝ) : ℂ) •
            Planar.transportGroupW m (-1 * clampB B r) (A0 (V r))) := by
      intro t
      rw [dysonTerm_succ_planarRelTransportRe]
      simp_rw [planarRelTransportRe_apply_eq]
      have hL := ContinuousLinearMap.intervalIntegral_comp_comm
        (((Real.exp (-γ * clampB B t) : ℝ) : ℂ) • Planar.transportGroupW m (1 * clampB B t))
        (hφ.intervalIntegrable (μ := volume) s t)
      simpa only [smul_apply] using hL
    simp_rw [heq]
    exact continuous_expSmulTransport m (-γ) 1 hc
      (intervalIntegral.continuous_primitive (fun a b => hφ.intervalIntegrable (μ := volume) a b) s)

/-- **`DysonDefined` for `(planarRelTransportRe, A0)`** (proved): every iterated integrand is
continuous in the integration variable. -/
theorem dysonDefined_planarRelTransportRe (P : PlanarData) (m B : ℝ)
    (A0 : Planar.L2w m →L[ℂ] Planar.L2w m) :
    UnforcedLeray.B0104.DysonDefined (ι := Unit) B
      (fun _ => fun τ σ => planarRelTransportRe P m (clampB B τ) (clampB B σ))
      (fun _ _ => A0) := by
  intro k p s t _ _ x
  set γ := P.eigenvalue.re
  have hc := continuous_clampB B
  have hV := continuous_dysonTerm_planarRelTransportRe P m B A0 k s x
  refine Continuous.intervalIntegrable ?_ s t
  simp_rw [planarRelTransportRe_apply_eq]
  exact continuous_expSmulTransport m (-γ) 1 continuous_const
    (continuous_expSmulTransport m γ (-1) hc (A0.continuous.comp hV))

/-- Planar dual pairing `ℓ_i(Φ) = ∫ λ_i Φ` (the planar limit of `movLamPair`, SP 2891-2897). -/
def planarLamPair (κ : PlanarFrameKernels) (i : Fin 2) (Φ : ℂ → ℂ) : ℂ :=
  ∫ y, κ.lamP i y * Φ (planeToC y)

/-- The seed pair `λ₀ = λ`, `λ₁ = λ̄` (SP 593-597). -/
def seedEigen (lam : ℂ) (i : Fin 2) : ℂ :=
  if i = 0 then lam else starRingEnd ℂ lam

/-- **The planar damped interaction** (SP 2920-2927): `A0` acts on compactly supported smooth
fields as `A0 W = 𝒜 W + Σ_i (γ - 1 - λ_i) ℓ_i(W) e_i`, with `𝒜 = Planar.couplingW`,
`γ = Re P.eigenvalue` (the limit of `β₀ = movBeta0`), `e_i = κ.e i`, `ℓ_i = planarLamPair κ i`,
and `λ_i` the seed pair of the seed data of `κ` (`κ.e 0 = q`). This is
`𝒜 - 𝒫𝓛𝒫 + (γ - 1)𝒫`, the limit of `movLInt + movFrameRankPert`. -/
def IsPlanarDampedInt (κ : PlanarFrameKernels) (P : PlanarData) {m : ℝ} (hm : 1 < m)
    (A0 : Planar.L2w m →L[ℂ] Planar.L2w m) : Prop :=
  ∃ (lam : ℂ) (h_prof : ℝ → ℂ) (hh : MemLp h_prof 2 B0010.xGMeasure) (ℓ : B0010.XG →L[ℂ] ℂ),
    PartI.IsSeedXG lam (hh.toLp h_prof) ℓ ∧
    (∀ y, κ.e 0 y = PartI.seedPlanar h_prof (planeToC y)) ∧
    ∀ Φ : ℂ → ℂ, ContDiff ℝ ∞ Φ → HasCompactSupport Φ →
      ∀ W : Planar.L2w m, (⇑W =ᵐ[volume] Φ) →
        ⇑(A0 W) =ᵐ[volume] fun z =>
          Planar.couplingW hm W z +
            ∑ i : Fin 2, (((P.eigenvalue.re - 1 : ℝ) : ℂ) - seedEigen lam i) *
              planarLamPair κ i Φ * κ.e i (cToPlane z)

/-- **Leaf B1 (bounded extension, SP 2920-2925)**: `IsPlanarDampedInt` has a solution
(`couplingW` is bounded, `ℓ_i` is bounded on `Planar.L2w m` since `κ.lamP` is bounded and
`L²_m ⊂ L¹` for `m > 1`, and `e_i ∈ L²_m` by the Gaussian tails `κ.e_decay`). -/
def PlanarDampedIntExists (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ (m : ℝ) (hm : 1 < m), 8 < m →
    ∃ A0 : Planar.L2w m →L[ℂ] Planar.L2w m, IsPlanarDampedInt κ P hm A0

/-- **Leaf B2 (compactness, SP 2972-2974)**: the planar damped interaction is compact
(`couplingW` is compact: sector compactness `Planar.isCompactOperator_couplingSec` with sector
norms tending to zero; the `𝒫` terms have rank two). -/
def PlanarDampedIntCompact (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ (m : ℝ) (hm : 1 < m), 8 < m →
  ∀ A0 : Planar.L2w m →L[ℂ] Planar.L2w m, IsPlanarDampedInt κ P hm A0 →
    IsCompactOperator A0

/-- **Leaf B3 (planar relative evolution, SP 2926-2935, 2976-2980)**: the Dyson sum of
`(planarRelTransportRe, A0)` on `[0, B]` (defined by `dysonDefined_planarRelTransportRe`), which is
`U0(t,0) = e^{-γt}e^{t𝓛}𝒬 + e^{-t}𝒫`, obeys `‖U0 B 0‖ ≤ C₀ e^{-hB} + Cproj e^{-B}`. -/
def PlanarDampedDysonBound (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ (m : ℝ) (hm : 1 < m), 8 < m →
  ∀ C₀ h Cproj B : ℝ,
    0 < C₀ → 0 < h → h ≤ P.eigenvalue.re → 0 ≤ Cproj → 0 < B →
    SeedCtx κ P m C₀ h → SeedProjBdd κ P m Cproj →
    ∀ A0 : Planar.L2w m →L[ℂ] Planar.L2w m, IsPlanarDampedInt κ P hm A0 →
      ∀ U0 : Unit → ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m,
        UnforcedLeray.B0104.IsDysonSum B
          (fun _ => fun τ σ => planarRelTransportRe P m (clampB B τ) (clampB B σ))
          (fun _ _ => A0) U0 →
        ‖U0 () B 0‖ ≤ C₀ * Real.exp (-h * B) + Cproj * Real.exp (-B)

/-- **Leaf B4 (norm convergence of the interaction, SP 2898-2925, 2974-2978)**: in the successive
limit, uniformly in train, entrance time and `r ∈ [0, B]`, the damped complement interaction
converges in operator norm to the planar damped interaction (image and dual estimates:
`movLInt → 𝒜`, `E → e`, `Λ → ℓ`, `H₀ → ℓ𝓛`, `K₀ → 𝓛e`, `M₀ → ℓ𝓛e`, `β₀ → γ`, cell
truncation of Gaussian-decaying fields). -/
def PlanarDampedIntLimit (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ (m : ℝ) (hm : 1 < m), 8 < m →
  ∀ A0 : Planar.L2w m →L[ℂ] Planar.L2w m, IsPlanarDampedInt κ P hm A0 →
  ∀ K B ε : ℝ, 0 < B → 0 < ε →
    SuccBlock κ m K B fun ν tr t₁ _t₂ =>
      ∀ A_rel : ℝ → Planar.L2w m →L[ℂ] Planar.L2w m,
        IsDampedComplBlockInt κ P ν m tr t₁ B A_rel →
        ∀ r ∈ Icc (0 : ℝ) B, ‖A_rel r - A0‖ < ε

/-- **Assembly** of `RelPlanarInteraction κ` from the four leaves, with the constant interaction
`A0 r = A0` (its range is a point, hence totally bounded). -/
theorem relPlanarInteraction_of (κ : PlanarFrameKernels) (h1 : PlanarDampedIntExists κ)
    (h2 : PlanarDampedIntCompact κ) (h3 : PlanarDampedDysonBound κ)
    (h4 : PlanarDampedIntLimit κ) : RelPlanarInteraction κ := by
  intro hκ P hP m hm K C₀ h Cproj B hC₀ hh hhle hCp hB hSeed hProj
  have hm1 : (1 : ℝ) < m := by linarith
  obtain ⟨A0, hA0⟩ := h1 hκ P hP m hm1 hm
  have hbd := h3 hκ P hP m hm1 hm C₀ h Cproj B hC₀ hh hhle hCp hB hSeed hProj A0 hA0
  refine ⟨fun _ => A0, fun _ => h2 hκ P hP m hm1 hm A0 hA0, ?_,
    dysonDefined_planarRelTransportRe P m B A0, hbd, ?_⟩
  · refine (Set.finite_singleton A0).totallyBounded.subset ?_
    rintro _ ⟨r, rfl⟩
    exact Set.mem_singleton _
  · intro ε hε
    exact h4 hκ P hP m hm1 hm A0 hA0 K B ε hB hε

end PlanarB

end OrgSplit3
end BlockPropagatorInteriorSub
end UnforcedLeray.Short.IIIa

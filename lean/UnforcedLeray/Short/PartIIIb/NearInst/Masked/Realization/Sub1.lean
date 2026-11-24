import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Sub

/-!
# Leaves of `KernelFormulaSmooth` (source 3586-3626, `sep:resolvent`)

Source of record: `the November 2 reference manuscript`.

`KernelFormulaSmooth` is proved by chaining, for `F = toX (P_3D div M)`, `M = outerField ε⁻¹ T`
(`CartStress = physRes F`, `h = νε²`, `θ_t = h(eᵗ-1)`, `l = e^{-t/2}`, `R = ε⁻¹`):

1. `KF2` (Laplace integral, 3617: `physRes = ∫_0^∞ e^{-μt}S_ε(t)dt`, with `KF1`, the pointwise
   outer semigroup `e^{t/2}[e^{θ_tΔ}F(·, τ-t)](e^{t/2}x)`, 3613-3615; both for `ν, ε > 0`);
2. `KF3` (heat-Leray, 3597-3601, 3618-3619: `e^{θΔ}P div M = ∇K_θ : M`);
3. `KF6`, `KF7` (periodic phase bookkeeping);
4. `KF5a` (space dilations, `KF4` homogeneity of `∇K_θ`: scaling by `R`, `e^{t/2}`; "heat scaling
   contributes `λ³`, the divergence `λ`", 3615-3616) and `KF5b` (the substitution `λ = e^{-t/2}`,
   `dt = -2 dλ/λ`, `e^{-μt} = λ^{2μ}`; "`-2dλ/λ`", 3616).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Masked

/-- The integrand of `IIIa.sepW` (`sep:resolvent`, 3622-3626): `∫ ∇K_{ν(1-l²)}(y - l z) : T(z, τ) dz`
in component `i`. -/
def sepInner (ν l : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (y : Space) (τ : ℝ)
    (i : Fin 3) : ℂ :=
  ∫ z : Space, ∑ j : Fin 3, ∑ k : Fin 3,
    ((fderiv ℝ (fun x => UnforcedLeray.Short.IIIa.heatLerayK (ν * (1 - l ^ 2)) i j x) (y - l • z)
      (UnforcedLeray.coordinateVector k) : ℝ) : ℂ) * ((T τ z j k : ℝ) : ℂ)

theorem sepW_eq_sepInner (ν : ℝ) (μ : ℂ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (y : Space) (τ : ℝ) (i : Fin 3) :
    UnforcedLeray.Short.IIIa.sepW ν μ T y τ i =
      -2 * ∫ l in Ioo (0 : ℝ) 1, (l : ℂ) ^ (2 * μ + 2) * sepInner ν l T y (τ + 2 * Real.log l) i :=
  rfl

/-- `(∇K_θ : M)_i(x, τ) = ∫ ∑_{jk} ∂_k(K_θ)_{ij}(x - z) M_{jk}(z, τ) dz` for the outer field
`M(z, τ) = T(τ, R z)` (3597-3601, 3618-3619). -/
def convTerm (θ R : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (x : Space) (τ : ℝ)
    (i : Fin 3) : ℂ :=
  ∫ z : Space, ∑ j : Fin 3, ∑ k : Fin 3,
    ((fderiv ℝ (fun x => UnforcedLeray.Short.IIIa.heatLerayK θ i j x) (x - z)
      (UnforcedLeray.coordinateVector k) : ℝ) : ℂ) * ((T τ (R • z) j k : ℝ) : ℂ)

/-- **KF1** (3613-3615, "The free semigroup is `e^{h/2}[e^{ν(e^h-1)Δ}f(τ-h)](e^{h/2}y)`"): for
`νε² > 0` (source `ν > 0`, `ε > 0`; the hypothesis of `B0223.Sop_rep`, so that the heat time
`θ_t = νε²(eᵗ-1)` is positive for `t > 0`) the outer semigroup
`S_ε(t) = e^{-t/4} dilN(e^{t/2}) e^{θ_tΔ} transC t` (`B0223.Sop`, `Sop_rep`, `Sop_apply`,
`coeFn_dilN`, `heatC_rep`, `coeFn_transC`) acts pointwise a.e. by
`e^{t/2}[e^{θ_tΔ}F(·, τ-t)](e^{t/2}x)`, componentwise.  (Without `0 < νε²` it is false:
`heatG 0 = 0` while `S_ε(t)F ≠ 0`, `Sub2.not_KF1_body`.) -/
def KF1 : Prop :=
  ∀ (ν ε : ℝ) (P : ℝ) [Fact (0 < P)] (F : UnforcedLeray.B0223.X UnforcedLeray.B0223.SpaceC P)
    (t : ℝ), 0 < ν * ε ^ 2 → 0 < t →
    ∀ᵐ w : UnforcedLeray.B0223.PSpace P ∂volume, ∀ i : Fin 3,
      (UnforcedLeray.B0223.Sop (ν * ε ^ 2) t F w) i =
        ((Real.exp (t / 2) : ℝ) : ℂ) * ∫ y : Space,
          ((UnforcedLeray.Short.IIIa.heatG (ν * ε ^ 2 * (Real.exp t - 1)) y : ℝ) : ℂ) *
            (F (Real.exp (t / 2) • w.1 - y, w.2 - (t : AddCircle P))) i

/-- **KF2** (3617, "In its Laplace integral"): for `ν > 0`, `ε > 0`,
`physRes = ∫_0^∞ e^{-μt}S_ε(t)dt` (a Bochner integral in `L²`, `Infra.ExpSemigroup.laplace`),
evaluated pointwise a.e. with the explicit semigroup of `KF1` (joint measurability of the explicit
integrand and Fubini for the `L²`-valued Bochner integral; uses `KF1`).  The body is that of
`Sub2.KF2pos`; without `ε > 0` it is false (`Sub2.not_KF2_body`). -/
def KF2 : Prop :=
  ∀ (ν ε : ℝ) (hν : 0 < ν), 0 < ε → ∀ (P : ℝ) [Fact (0 < P)] (μ : ℂ), -(1 / 4) < μ.re →
    ∀ F : UnforcedLeray.B0223.X UnforcedLeray.B0223.SpaceC P,
    ∀ᵐ w : UnforcedLeray.B0223.PSpace P ∂volume, ∀ i : Fin 3,
      (UnforcedLeray.B0223.physRes hν ε μ F w) i =
        ∫ t in Ioi (0 : ℝ), Complex.exp (-μ * t) *
          (((Real.exp (t / 2) : ℝ) : ℂ) * ∫ y : Space,
            ((UnforcedLeray.Short.IIIa.heatG (ν * ε ^ 2 * (Real.exp t - 1)) y : ℝ) : ℂ) *
              (F (Real.exp (t / 2) • w.1 - y, w.2 - (t : AddCircle P))) i)

/-- **KF3** (3597-3601, 3618-3619: "the heat-Leray kernel `K_t = δG_t + ∂∂∫_t^∞G_a da`", and
"integrate the tensor divergence by parts"): for `F = toX (P_3D div M)`,
`M(z, τ) = T(τ, ε⁻¹z)` smooth, periodic, compactly supported in `z`, the heat flow of `F` is
`e^{θΔ}F(x, s) = (∇K_θ : M)(x, s)` for all `x`, `θ > 0`, a.e. phase `s` (`T` is `P`-periodic, so the
phase `τ` is `(toCell P (0, s)).2`).  Route: `P_3D` is the orthogonal projection onto the
solenoidal fields, `P_3D div M = div M - ∇q` with `Δq = div div M`, so
`e^{θΔ}P_3D div M` has Fourier symbol `(I - ξξᵀ/|ξ|²) e^{-θ|ξ|²} iξ·M̂` and `K_θ` is its kernel. -/
def KF3 : Prop :=
  ∀ (ν ε c P : ℝ) [Fact (0 < P)] (hν : 0 < ν), 0 < ε → 0 < c → ∀ (hP : P = 2 * ε * c)
    (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ), IsCartTest P T →
    ∀ hM : MemLp (cartDiv (outerField ε⁻¹ T)) 2 (UnforcedLeray.B0220.physMeasure ε c),
    ∀ᵐ s : AddCircle P ∂volume, ∀ (x : Space) (θ : ℝ), 0 < θ → ∀ i : Fin 3,
      ∫ y : Space, ((UnforcedLeray.Short.IIIa.heatG θ y : ℝ) : ℂ) *
          ((UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.toX hP
            (UnforcedLeray.B0226.P3D ε c (hM.toLp (cartDiv (outerField ε⁻¹ T))))
              : UnforcedLeray.B0223.PSpace P → UnforcedLeray.B0223.SpaceC) (x - y, s)) i =
        convTerm θ ε⁻¹ T x (UnforcedLeray.B0223.toCell P (0, s)).2 i

/-- **KF4** (homogeneity of the heat-Leray kernel, 3604-3606): `K_t(ρx) = ρ^{-3}K_{t/ρ²}(x)`, so
`∇K_θ(ρ x) = ρ^{-4}∇K_{θ/ρ²}(x)` for `ρ, θ > 0`. -/
def KF4 : Prop :=
  ∀ (ρ θ : ℝ), 0 < ρ → 0 < θ → ∀ (i j k : Fin 3) (x : Space),
    fderiv ℝ (fun x => UnforcedLeray.Short.IIIa.heatLerayK θ i j x) (ρ • x)
        (UnforcedLeray.coordinateVector k) =
      (ρ ^ 4)⁻¹ * fderiv ℝ (fun x => UnforcedLeray.Short.IIIa.heatLerayK (θ / ρ ^ 2) i j x) x
        (UnforcedLeray.coordinateVector k)

/-- **KF5a** (3614-3616: "Heat scaling contributes `λ³`, the divergence contributes `λ`, and the
semigroup amplitude and differential contribute `λ^{-1}`"): with `l = e^{-t/2}`, `R = ε⁻¹`,
the substitution `z ↦ z/R` in the convolution (so `dz` gives `R^{-3}`) and the homogeneity `KF4`
(twice: `ρ = 1/R`, then `ρ = 1/l`) give
`e^{t/2} (∇K_{νε²(eᵗ-1)} : T(τ, R·))(e^{t/2}x) = R l³ ∫ ∇K_{ν(1-l²)}(Rx - l z) : T(τ, z) dz`. Uses `KF4`. -/
def KF5a : Prop :=
  ∀ (ν ε : ℝ), 0 < ν → 0 < ε → ∀ (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (x : Space) (τ t : ℝ),
    0 < t → ∀ i : Fin 3,
      ((Real.exp (t / 2) : ℝ) : ℂ) *
          convTerm (ν * ε ^ 2 * (Real.exp t - 1)) ε⁻¹ T (Real.exp (t / 2) • x) τ i =
        ((ε⁻¹ * Real.exp (-t / 2) ^ 3 : ℝ) : ℂ) *
          sepInner ν (Real.exp (-t / 2)) T (ε⁻¹ • x) τ i

/-- **KF5b** (3616, "`-2dλ/λ`"; `sep:resolvent` 3620-3626): the change of variables
`l = e^{-t/2}` (`dt = -2 dl/l`, `e^{-μt} = l^{2μ}`, `τ - t = τ + 2 log l`) from `(0, ∞)` onto
`(0, 1)` in the Bochner integral. -/
def KF5b : Prop :=
  ∀ (ν : ℝ) (μ : ℂ) (R : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (y : Space) (τ : ℝ)
    (i : Fin 3),
    ∫ t in Ioi (0 : ℝ), Complex.exp (-μ * t) *
        (((R * Real.exp (-t / 2) ^ 3 : ℝ) : ℂ) * sepInner ν (Real.exp (-t / 2)) T y (τ - t) i) =
      (R : ℂ) * (2 * ∫ l in Ioo (0 : ℝ) 1, (l : ℂ) ^ (2 * μ + 2) *
        sepInner ν l T y (τ + 2 * Real.log l) i)

/-- **KF6** (phase bookkeeping): for `P`-periodic `T`, `T` at the cell representative of the shifted
phase `s - t` is `T` at the shifted representative: `T (toCell P (0, s - t)).2 = T ((toCell P (0, s)).2 - t)`. -/
def KF6 : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ),
    (∀ (τ : ℝ) (z : Space), T (τ + P) z = T τ z) →
    ∀ (s : AddCircle P) (t : ℝ),
      T (UnforcedLeray.B0223.toCell P (0, s - (t : AddCircle P))).2 =
        T ((UnforcedLeray.B0223.toCell P (0, s)).2 - t)

/-- **KF7** (null sets of the circle pull back to null sets of `ℝ`): for `N ⊆ ℝ/Pℤ` null and `s`,
`{t | s - t ∈ N}` is null (it is a countable union of translates of a null set, `AddCircle`). -/
def KF7 : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (N : Set (AddCircle P)), volume N = 0 → ∀ s : AddCircle P,
    volume {t : ℝ | s - (t : AddCircle P) ∈ N} = 0


/-! ## The assembly -/

theorem convTerm_congr (θ R : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (x : Space)
    {τ₁ τ₂ : ℝ} (h : T τ₁ = T τ₂) (i : Fin 3) : convTerm θ R T x τ₁ i = convTerm θ R T x τ₂ i := by
  unfold convTerm
  rw [h]

/-- **`KernelFormulaSmooth` from the leaves.** -/
theorem kernelFormulaSmooth_of (h2 : KF2) (h3 : KF3) (h5a : KF5a) (h5b : KF5b) (h6 : KF6)
    (h7 : KF7) : KernelFormulaSmooth := by
  intro ν ε c P _ hν hε hc hP μ hμ T hT hM
  set F := toX hP (UnforcedLeray.B0226.P3D ε c (hM.toLp (cartDiv (outerField ε⁻¹ T)))) with hF
  have hCS : (CartStress hν hP μ (outerField ε⁻¹ T) hM :
      UnforcedLeray.B0223.PSpace P → UnforcedLeray.B0223.SpaceC) =
      (UnforcedLeray.B0223.physRes hν ε μ F : UnforcedLeray.B0223.PSpace P →
        UnforcedLeray.B0223.SpaceC) := rfl
  rw [hCS]
  have a2 := h2 ν ε hν hε P μ hμ F
  have a3 := h3 ν ε c P hν hε hc hP T hT hM
  have a3' : ∀ᵐ w : UnforcedLeray.B0223.PSpace P ∂volume, ∀ (x : Space) (θ : ℝ), 0 < θ →
      ∀ i : Fin 3, ∫ y : Space, ((UnforcedLeray.Short.IIIa.heatG θ y : ℝ) : ℂ) *
          ((F : UnforcedLeray.B0223.PSpace P → UnforcedLeray.B0223.SpaceC) (x - y, w.2)) i =
        convTerm θ ε⁻¹ T x (UnforcedLeray.B0223.toCell P (0, w.2)).2 i :=
    (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure Space))
      (ν := (volume : Measure (AddCircle P)))).ae a3
  filter_upwards [a2, a3'] with w hw2 hw3
  ext i
  rw [hw2 i]
  set N : Set (AddCircle P) := {s : AddCircle P | ¬ ∀ (x : Space)
      (θ : ℝ), 0 < θ → ∀ i : Fin 3, ∫ y : Space, ((UnforcedLeray.Short.IIIa.heatG θ y : ℝ) : ℂ) *
          ((F : UnforcedLeray.B0223.PSpace P → UnforcedLeray.B0223.SpaceC) (x - y, s)) i =
        convTerm θ ε⁻¹ T x (UnforcedLeray.B0223.toCell P (0, s)).2 i} with hN
  have hNull := h7 P N (ae_iff.1 a3) w.2
  have h0 : ∀ᵐ t : ℝ, w.2 - (t : AddCircle P) ∉ N := by
    rw [ae_iff]
    simpa using hNull
  have key : ∫ t in Ioi (0 : ℝ), Complex.exp (-μ * t) *
      (((Real.exp (t / 2) : ℝ) : ℂ) * ∫ y : Space,
        ((UnforcedLeray.Short.IIIa.heatG (ν * ε ^ 2 * (Real.exp t - 1)) y : ℝ) : ℂ) *
          ((F : UnforcedLeray.B0223.PSpace P → UnforcedLeray.B0223.SpaceC)
            (Real.exp (t / 2) • w.1 - y, w.2 - (t : AddCircle P))) i) =
      ∫ t in Ioi (0 : ℝ), Complex.exp (-μ * t) *
        (((ε⁻¹ * Real.exp (-t / 2) ^ 3 : ℝ) : ℂ) * sepInner ν (Real.exp (-t / 2)) T (ε⁻¹ • w.1)
          ((UnforcedLeray.B0223.toCell P w).2 - t) i) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae h0, ae_restrict_mem measurableSet_Ioi] with t ht htpos
    have ht' : ∀ (x : Space) (θ : ℝ), 0 < θ → ∀ i : Fin 3,
        ∫ y : Space, ((UnforcedLeray.Short.IIIa.heatG θ y : ℝ) : ℂ) *
          ((F : UnforcedLeray.B0223.PSpace P → UnforcedLeray.B0223.SpaceC)
            (x - y, w.2 - (t : AddCircle P))) i =
        convTerm θ ε⁻¹ T x (UnforcedLeray.B0223.toCell P (0, w.2 - (t : AddCircle P))).2 i := by
      have h' := ht
      rw [hN] at h'
      simpa using h'
    have htp : (0 : ℝ) < t := htpos
    have hθ : 0 < ν * ε ^ 2 * (Real.exp t - 1) := by
      have : 0 < Real.exp t - 1 := by linarith [Real.add_one_lt_exp htp.ne']
      positivity
    have e1 := h5a ν ε hν hε T w.1 ((UnforcedLeray.B0223.toCell P w).2 - t) t htp i
    rw [ht' _ _ hθ i, convTerm_congr _ _ T _ (h6 P T hT.periodic w.2 t) i, ← e1]
    rfl
  rw [key, h5b ν μ ε⁻¹ T (ε⁻¹ • w.1) (UnforcedLeray.B0223.toCell P w).2 i]
  simp only [kernelField, sepW_eq_sepInner]
  ring

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

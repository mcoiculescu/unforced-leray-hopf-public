import UnforcedLeray.Short.PartIIb.Sub.G4_3_org

/-!
# Part II-b, `PartII-b:G4/3/4` (`InletBPtw`): decomposition

Source of record: `the November 2 reference manuscript` (SP) 1919-1921, 2007-2012
(`K_ε = s B_ε T_ε`), 2370-2374, 2419.

The pointwise identity `U_raw·∇(N_vE) + (N_vE)·∇U_raw = N_v(sB_εE)` splits into

* `ChartAdvPtw`: the general polarized advection identity for two no-swirl ring lifts in the chart
  (`∂_ρ(√s f) = sQ_εf`, `∂_z(√s f) = s∂_ηf`; SP 1919-1921; `Axi.advection_liftMer`);
* `RawProfDiffAt`, `InletProfileDiffAt`: differentiability of the two profiles at chart points
  with `s > 0` (`BgRegime.train_stream_smooth`; the inlet profile is `C^∞`, as in `inletContDiff`).

`inletBPtw_of` (proved here) combines them: local replacement `U_raw = N_v b_raw` off the axis
(`Params.raw_eq_off_axis`), linearity of `B_ε` in the inlet profile, and `NvC (cplx f) = realC (Nv f)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412

/-- **The polarized advection identity for ring lifts** (SP 1919-1921, 2007-2012): off the axis,
for two meridional profiles `b, d` differentiable at the chart point, with `ε = R⁻¹`,
`(N_vb·∇)N_vd + (N_vd·∇)N_vb = N_v(s[b_r Q_εd + b_z ∂_ηd + d_r Q_εb + d_z ∂_ηb])`
(`∂_ρ(√s f) = sQ_εf`, `∂_z(√s f) = s∂_ηf`; no hoop term, no swirl). -/
def ChartAdvPtw : Prop :=
  ∀ (R : ℝ), 0 < R → ∀ (b d : Coord → Axi.Merid) (τ : ℝ) (y : Space), y ∉ Axi.axis →
    DifferentiableAt ℝ b (Axi.chart R τ y) → DifferentiableAt ℝ d (Axi.chart R τ y) →
      advT (fun x => realC (Axi.Nv R b x.1 x.2)) (fun x => realC (Axi.Nv R d x.1 x.2)) (τ, y) +
        advT (fun x => realC (Axi.Nv R d x.1 x.2)) (fun x => realC (Axi.Nv R b x.1 x.2)) (τ, y) =
      realC (Axi.Nv R (fun m => m.1 • (b m 0 • qEps R⁻¹ d m + b m 1 • Axi.dEta d m +
        (d m 0 • qEps R⁻¹ b m + d m 1 • Axi.dEta b m))) τ y)

/-- **Differentiability of the raw profile** `b_raw = (v₁, v₂ + εH)` on `s > 0`
(`BgRegime.train_stream_smooth`, SP 1206-1216, 2419). -/
def RawProfDiffAt : Prop :=
  ∀ (dm dp : ℝ) (p : Params) (d : ℝ), BgRegime p d dm dp →
    ∀ m : Coord, 0 < m.1 → DifferentiableAt ℝ (rawProf p) m

/-- **Differentiability of the inlet profiles** (smooth everywhere: `ringStreamProfile` of the
`C^∞` cutoff stream; the argument of `inletContDiff`). -/
def InletProfileDiffAt : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      ∀ (i : Fin 2) (m : Coord), DifferentiableAt ℝ (p.inletProfile i) m

/-! ## Glue -/

theorem advT_congr {u u' Φ Φ' : ℝ × Space → CVec3} {x : ℝ × Space} (hu : u x = u' x)
    (hΦ : Φ =ᶠ[𝓝 x] Φ') : advT u Φ x = advT u' Φ' x := by
  unfold advT dy
  rw [hΦ.fderiv_eq, hu]

theorem Nv_zero_fun (R : ℝ) (τ : ℝ) (y : Space) :
    Axi.Nv R (fun _ => (0 : Axi.Merid)) τ y = 0 := by
  simp [Axi.Nv]

theorem NvC_cplx (R : ℝ) (f : Coord → Axi.Merid) (x : ℝ × Space) :
    NvC R (cplx f) x = realC (Axi.Nv R f x.1 x.2) := by
  have h1 : (fun z => reM (cplx f z)) = f := by
    funext z; ext i; simp [reM, cplx]
  have h2 : (fun z => imM (cplx f z)) = fun _ => (0 : Axi.Merid) := by
    funext z; ext i; simp [imM, cplx]
  unfold NvC
  rw [h1, h2, Nv_zero_fun]
  have : realC (0 : Space) = 0 := by
    ext i; simp [realC_apply]
  simp [this]

theorem realC_add' (x y : Space) : realC (x + y) = realC x + realC y := by
  ext i; simp [realC_apply]

theorem realC_smul' (a : ℝ) (x : Space) : realC (a • x) = (a : ℂ) • realC x := by
  ext i; simp [realC_apply]

theorem inletBPtw_of (h1 : ChartAdvPtw) (h2 : RawProfDiffAt) (h3 : InletProfileDiffAt) :
    InletBPtw := by
  intro Sig lam q hSig hq dm dp hdm
  obtain ⟨ν₁, hν₁, H1⟩ := h3 Sig lam q hSig hq dm dp hdm
  refine ⟨ν₁, hν₁, ?_⟩
  intro p d hreg hν hs hm α τ y hy
  have hdi := H1 p d hreg hν hs hm
  have hRne : p.R ≠ 0 := p.R_pos.ne'
  have hpos : 0 < (Axi.chart p.R τ y).1 := Axi.age_pos hRne hy
  have hb := h2 dm dp p d hreg _ hpos
  have hE0 := hdi 0 (Axi.chart p.R τ y)
  have hE1 := hdi 1 (Axi.chart p.R τ y)
  set E : Coord → Axi.Merid := fun m => α 0 • p.inletProfile 0 m + α 1 • p.inletProfile 1 m
    with hEdef
  have hE : DifferentiableAt ℝ E (Axi.chart p.R τ y) :=
    (hE0.const_smul (α 0)).fun_add (hE1.const_smul (α 1))
  have hεR : p.ε⁻¹ = p.R := rfl
  have hmain := h1 p.R p.R_pos (rawProf p) E τ y hy hb hE
  -- local replacement of the raw field
  have hopen : IsOpen {x : ℝ × Space | x.2 ∉ Axi.axis} :=
    Axi.isOpen_compl_axis.preimage continuous_snd
  have hUev : p.Ufun =ᶠ[𝓝 (τ, y)]
      (fun x => realC (Axi.Nv p.R (rawProf p) x.1 x.2)) := by
    filter_upwards [hopen.mem_nhds (show (τ, y) ∈ _ from hy)] with x hx
    show realC (p.raw x.1 x.2) = _
    rw [p.raw_eq_off_axis x.1 x.2 hx]
    rfl
  have hIC : inletC p α =
      fun x => realC (Axi.Nv p.R E x.1 x.2) := by
    funext x
    unfold inletC
    rw [Fin.sum_univ_two]
    simp only [Params.Efun, Params.inlet, hEdef]
    have : Axi.Nv p.R (fun m => α 0 • p.inletProfile 0 m + α 1 • p.inletProfile 1 m) x.1 x.2 =
        α 0 • Axi.Nv p.R (p.inletProfile 0) x.1 x.2 +
          α 1 • Axi.Nv p.R (p.inletProfile 1) x.1 x.2 := by
      have := Axi.Nv_add p.R (α 0 • p.inletProfile 0) (α 1 • p.inletProfile 1) x.1 x.2
      rw [Axi.Nv_smul, Axi.Nv_smul] at this
      exact this
    rw [this, realC_add', realC_smul', realC_smul']
  have e1 : advT p.Ufun (inletC p α) (τ, y) =
      advT (fun x => realC (Axi.Nv p.R (rawProf p) x.1 x.2))
        (fun x => realC (Axi.Nv p.R E x.1 x.2)) (τ, y) := by
    rw [hIC]
    exact advT_congr (by simpa using hUev.eq_of_nhds) (Filter.EventuallyEq.refl _ _)
  have e2 : advT (inletC p α) p.Ufun (τ, y) =
      advT (fun x => realC (Axi.Nv p.R E x.1 x.2))
        (fun x => realC (Axi.Nv p.R (rawProf p) x.1 x.2)) (τ, y) := by
    rw [hIC]
    exact advT_congr rfl hUev
  have hRε : p.R⁻¹ = p.ε := by simp [Params.R]
  rw [hRε] at hmain
  rw [e1, e2, hmain]
  have hcol : (fun m : Coord => ∑ i : Fin 2, ((α i : ℝ) : ℂ) • cplx (colIntR p i) m) =
      cplx (fun m => ∑ i : Fin 2, α i • colIntR p i m) := by
    funext m; ext j; simp [cplx, Fin.sum_univ_two]
  rw [hcol, NvC_cplx]
  congr 1
  unfold Axi.Nv
  congr 2
  show _ = ∑ i : Fin 2, α i • colIntR p i (Axi.chart p.R τ y)
  rw [Fin.sum_univ_two]
  set m0 := Axi.chart p.R τ y with hm0
  have hD : ∀ v, fderiv ℝ E m0 v = α 0 • fderiv ℝ (p.inletProfile 0) m0 v +
      α 1 • fderiv ℝ (p.inletProfile 1) m0 v := by
    intro v
    have h : HasFDerivAt E (α 0 • fderiv ℝ (p.inletProfile 0) m0 +
        α 1 • fderiv ℝ (p.inletProfile 1) m0) m0 :=
      (hE0.hasFDerivAt.const_smul (α 0)).add (hE1.hasFDerivAt.const_smul (α 1))
    rw [h.fderiv]
    simp
  have hEv : E m0 = α 0 • p.inletProfile 0 m0 + α 1 • p.inletProfile 1 m0 := rfl
  simp only [colIntR, bEps, qEps, kAge, Axi.dS, Axi.dQ, Axi.dEta, hD, hEv]
  ext j
  fin_cases j <;> simp <;> ring

end UnforcedLeray.Short.IIb

import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.FlatUniform
import UnforcedLeray.Short.PartIIIb.NearInst.Body.Proofs.BodyRealForms
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_6
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Levels

/-!
# `PartIII-b:IIIb-D3/2/G5/org`: the Newton/Taylor comparison `FlatUnif.FlatNewtonComparison`

Source of record: `the November 2 reference manuscript` (73 pages): proof of
`source-class:flat-limit` 4846-4907 (moments 4848-4857, analytical tail 4859-4877, mean-value
remainder 4879-4892, stream cutoff and transition 4894-4901, display 4902-4907); `𝒦^flat = 𝓛𝔗`
4761-4763, 4804-4806; `ℓ_μ` 4584-4587; `a_μ` 4807-4811; `𝒜_ν`, `A_*` 4582-4583; flat near
layer `D₀ = I + M₀S₀` 3874-3887 (`near:flat-bound`).

`FlatNewtonComparison D` is assembled (`flatNewtonComparison_of`) from three named inputs.

* `FlatNearUnit D` : the flat near operator `D₀ = I + M₀S₀` of the pinned near operators is a unit
  at the large levels on the window (3874-3887).  `SeqData.RepairStanding` records the curved unit
  `D_N` (`near`, from `NearSolverC`) but not `D₀`; without a unit `D₀` the column pin `ColumnPin`
  (`IsFlatDuhamelColumn`, a statement about every realization of the flat near operators) says
  nothing about `D.flat n`.
* `NewtonTaylor as K χo χy` : the receiver-level Newton/Taylor comparison for an arbitrary old thin
  tensor `M` with finite `N₀` (4859-4901), pointwise in the age `s`:
  `e^{-a_s s}s^{-5/2}Σ_{j≤6}|(s∂_s)^j(𝓛M - ℓ_μ(M)a_μ)(s)| ≤ C ε³[N₁^χ(M) + P_ν e^{-4a_s/(5ν)}N₀^χ(M)]`,
  `N_j^χ(M) = ∫_{u>1.2/ν} u^{-3/2-j/2} χ_o(νu) ⨍_cell|M|` (`oldN0w`, `oldN1w`).
* `FrakTMoments D` : for `M = 𝔗_{μ,ν}A` of the level, `M` is an old thin tensor with finite `N₀`
  and `N₁^χ(M) ≤ C𝒜_νν‖A‖`, `N₀^χ(M) ≤ C𝒜_ν‖A‖` uniformly on the window (4848-4854: the uniform
  source theorem, i.e. `flat-return:all-moments` 4637-4640 at `B = B_{μ,ν}[A]`).

**On the earlier-old part.**  The source splits `M` at `u_o = ν^{-3/2}` (4855-4857, 4898-4901) and
bounds the earlier-old field crudely by `P_νA_*e^{-γ'/√ν}`.  `NewtonTaylor` does not split: on the
whole old region `u > 1.2/ν` the source radius is `ρ = u^{-1/2} < (ν/1.2)^{1/2}`, and the receiver
radius is `r = s^{-1/2} ≥ (5ν/4)^{1/2}` where `χ_y ≡ 1` (`s ≤ 4/(5ν)`), so `ρ/r ≤ (2/3)^{1/2}`: the
mean-value remainder of `D⁴N(x - t(x',0)) - D⁴N(x)` is `≤ C tρ r^{-6}` with `C` depending only on
this fixed fractional gap ("fixed fractional gap", 4898-4899), and its radial first moment is
`N₁^χ` (4879-4884).  The target keeps the `P_νe^{-γ'/√ν}` term; it is not needed.

**Part (i), the pin** (`kflatPin_of`, proved here from `FlatNearUnit`): at large levels
`ι(𝒦^flat A) = 𝓛(𝔗(ιA))` for the pinned `KflatOp` (an `epsilon`), because the composite
`𝓛 ∘ T₀ ∘ F` (`T₀ = flatColG R₀`) satisfies the pin: the computation of
`NearInst.concreteBase_isFlatColumnKflat` (`NearInst/Link/Seq.lean`), with `𝓛`, `F_A` and the
actual near operators from `RepairStanding.pins`, `R₀` from `NearInst.Body.bodyRealForms`, the unit
`D₀` from `FlatNearUnit` and the column from `ColumnPin`.

Assembly: the task `PartIII-b:IIIb-D3/2/G5` states
`flatNewtonComparison D := FlatUnif.G5.flatNewtonComparison_of D (FlatUnif.G5.flatNearUnit D)
FlatUnif.G5.newtonTaylor (FlatUnif.G5.frakTMoments D)`.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G5

open ConcreteYF
open UnforcedLeray.Short.PartIIIb.NearInst (srcIso ten3Of trainMer)

/-! ## 1. The named inputs -/

/-- **The flat near layer is invertible at the large levels** (source 3874-3887 `near:flat-bound`:
`D₀ = I + M₀S₀`, `‖G⁻¹D₀⁻¹G‖ ≤ P_ν`; 3943-3951 `near:inverse-comparison`; 3560-3581
`D₀⁻¹ = I - M₀S_lin`): under the standing hypotheses, for large `n` and `z ∈ [-1,1]` the flat
operator `D₀` of the pinned near operators `nearOpsAt` of the level is a unit. -/
def FlatNearUnit (D : SeqData) : Prop :=
  ∀ dm dp : ℝ, D.RepairStanding dm dp →
    ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      IsUnit (nearOpsAt D.Pl D.K (D.level n) (D.mu n z)).D0

/-- **The `𝒦^flat` pin at the large levels** (source 4761-4763, 4804-4806): the pinned
`𝒦^flat_{μ,ν} = KflatOp` is `𝓛𝔗` read through `ι`. -/
def KflatPin (D : SeqData) : Prop :=
  ∀ dm dp : ℝ, D.RepairStanding dm dp → ColumnPin D →
    ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, ∀ A : AffSp D.K.as,
      affIota D.K.as (KflatOp D.K (D.level n) (D.mu n z) A) =
        KflatFun (D.flat n) (cOf (nu D n)) (nu D n) (retEps D.Pl D.σ₀ n) (D.mu n z) D.K.χo
          D.K.χy D.K.χf (affIota D.K.as A)

/-- `ℓ_μ(M) = ε³ I_T(M)/(8(μ+3/2))`, `I_T(M) = ∫ χ̂_o(νs) s^{-3/2}(1/c)∫_cell(2M_zz - M_rr)`
(source 4584-4587), for a stress `M` on the chart at cell size `c`; `ellMuAt D n` is its value at
the level (`ellMuAt_eq`). -/
def ellMuGen (c ν ε μ : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) : ℝ :=
  ε ^ 3 * (∫ s in Ioi (0 : ℝ), χo (ν * s) * s ^ (-(3 / 2 : ℝ)) *
      cellInt c (fun p => 2 * M (s, p) 2 2 - M (s, p) 0 0)) / (8 * (μ + 3 / 2))

theorem ellMuAt_eq (D : SeqData) (n : ℕ) (μ : ℝ) (M : Chart → Mat3) :
    ellMuAt D n μ M = ellMuGen (cOf (nu D n)) (nu D n) (retEps D.Pl D.σ₀ n) μ D.K.χo M := rfl

/-- The cut first old moment `N₁^χ(M) = ∫_{u>1.2/ν} u^{-2} χ_o(νu) ⨍_cell |M| du` (source
4848-4852 with `j = 1`; the radial first moment of `Σ_M` is `π N₁^χ`, 4879-4884); `oldN0w` is the
`j = 0` moment. -/
def oldN1w (c ν : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) : ℝ :=
  ∫ u in Ioi (6 / 5 / ν), u ^ (-(2 : ℝ)) * (χo (ν * u) * ∫ x, frob (M (u, x)) ∂(Cyl.avgμ c))

/-- **Newton/Taylor comparison of `𝓛` with the unit displacement** (source 4859-4901), for every
old thin tensor `M` with finite `N₀`, pointwise in the age `s > 0`, uniformly in `c`, `ε`, `μ ∈ K`
and `ν ≤ ν₀`:
`e^{-a_s s}s^{-5/2}Σ_{j≤6}|(s∂_s)^j(𝓛_{μ,ν}M - ℓ_μ(M)a_μ)(s)| ≤ Cε³[N₁^χ(M) + ν^{-k}e^{-4a_s/(5ν)}N₀^χ(M)]`.
On `s ≤ 4/(5ν)` (`χ_y ≡ 1`): the integrated Cartesian tensor `diag(T_h,T_h,T_z)`,
`T_z - T_h = (π/2)I_T`, `D²∂₃₃N(r,0,0) = (4πr⁵)⁻¹diag(-12,3,9)` (`newtonD2`), the dilation integrals
`∫₀¹t^{2μ+2} = (2μ+3)⁻¹` and the shifted field give `D_y(W^{(0)}_μ - W^{(0)}_{μ+1}) = ℓ_μ(M)a_μ`
(4859-4877); the mean-value remainder is `≤ C_kε³N₁^χ s³` (4879-4892, fixed fractional gap
`ρ/r ≤ (2/3)^{1/2}` on the whole old region), and `sup_s s^{1/2}e^{-a_s s} < ∞`.  On `s ≥ 4/(5ν)`
the cut field (stream cutoff, outward primitive) and `ℓ_μ(M)a_μ` are `≤ P_νε³N₀^χ s^{5/2}` and the
weight gives `e^{-4a_s/(5ν)}` (4894-4901). -/
def NewtonTaylor (as : ℝ) (K : Set ℝ) (χo χy : ℝ → ℝ) : Prop :=
  0 < as → IsCompact K → K ⊆ Ioo 0 (1 / 4) →
    ∃ (C ν₀ : ℝ) (k : ℕ), 0 ≤ C ∧ 0 < ν₀ ∧
      ∀ (c ν ε μ : ℝ), LHyp c ν ε μ χo χy → ν ≤ ν₀ → μ ∈ K →
        ∀ M : Chart → Mat3, OldThinFinite c ν M → ∀ s : ℝ, 0 < s →
          affTerm as 6 (Lpt c ν ε μ χo χy M - ellMuGen c ν ε μ χo M • aMuFun μ) s ≤
            C * ε ^ 3 * (oldN1w c ν χo M + ν⁻¹ ^ k * Real.exp (-(4 * as / 5) / ν) *
              oldN0w c ν χo M)

/-- `𝒜_ν = |N_ν|ν^{3+2μ}/c = |N_ν|ν^{5+2μ}` at `c = ν⁻²` (source 4582-4583), level `n`, window
point `z`; `A_* = ε³𝒜_ν` (`ast_eq`). -/
abbrev Anu (D : SeqData) (n : ℕ) (z : ℝ) : ℝ :=
  ‖Nnu D.Pl.eigenvalue D.Pl.kappa (nu D n)‖ * nu D n ^ (5 + 2 * D.mu n z)

/-- **The old moments of `𝔗A` at the levels** (source 4848-4854: "The uniform source theorem gives,
for `j=0,1`, `∫u^{-3/2-j/2}(χ_o/c)∫_cell|M| ≤ C_j𝒜_νν^j`", i.e. `flat-return:all-moments`
4637-4640 at `B = B_{μ,ν}[A]` with `‖B_{μ,ν}[A]‖_{a_s} ≤ C‖A‖_𝒜`, 4757-4760): under the standing
hypotheses and the column pin, for large `n`, `z ∈ [-1,1]` and `A ∈ 𝒜`, `M = 𝔗_{μ,ν}A` of the flat
setting of the level is an old thin tensor with finite `N₀` (4917-4927), and
`N₁^χ(M) ≤ C𝒜_νν‖A‖`, `N₀^χ(M) ≤ C𝒜_ν‖A‖`, one constant for the window. -/
def FrakTMoments (D : SeqData) : Prop :=
  ∀ dm dp : ℝ, D.RepairStanding dm dp → ColumnPin D →
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ n ≥ N, ∀ z ∈ Icc (-1 : ℝ) 1, ∀ A : AffSp D.K.as,
      OldThinFinite (cOf (nu D n)) (nu D n)
          (frakT (D.flat n) (nu D n) (D.mu n z) D.K.χf (affIota D.K.as A)) ∧
        oldN1w (cOf (nu D n)) (nu D n) D.K.χo
            (frakT (D.flat n) (nu D n) (D.mu n z) D.K.χf (affIota D.K.as A)) ≤
          C * Anu D n z * nu D n * ‖A‖ ∧
        oldN0w (cOf (nu D n)) (nu D n) D.K.χo
            (frakT (D.flat n) (nu D n) (D.mu n z) D.K.χf (affIota D.K.as A)) ≤
          C * Anu D n z * ‖A‖

/-! ## 2. Part (i): the pin -/

/-- **The `𝒦^flat` pin from the unit `D₀`** (source 4761-4763, 4804-4806, 4109-4111): the composite
`𝓛 ∘ T₀ ∘ F` satisfies the pin (the computation of `NearInst.concreteBase_isFlatColumnKflat`), so
the pinned `KflatOp` satisfies it. -/
theorem kflatPin_of (D : SeqData) (hU : FlatNearUnit D) : KflatPin D := by
  intro dm dp hst hpin
  have hω := hst.omega_ne
  have hσ0 := hst.sigma_pos
  have hσ1 := hst.sigma_lt
  obtain ⟨ν₄, hν₄, hBR⟩ := NearInst.Body.bodyRealForms (NearInst.winK D.σ₀)
    (NearInst.isCompact_winK _) (NearInst.winK_sub hσ0 hσ1) dm dp hst.dm_pos
  filter_upwards [NearInst.seq_levels D hω hσ0 hσ1 hst.actual hst.inlet hν₄, hst.pins,
    hU dm dp hst, hpin] with n hlev hpins hD0 hcol z hz A
  obtain ⟨hL, -, hνn, -, hμ⟩ := hlev
  set L : ReturnLevel := D.level n with hLdef
  set μ : ℝ := D.mu n z with hμdef
  obtain ⟨R0, hR0⟩ : ∃ R0 : Hsp (cOf L.ν) →L[ℝ] Hsp (cOf L.ν), NearInst.IsBodyTransport R0
      (UnforcedLeray.Short.PartIIa.T0flat (cOf_pos L.ν_pos) L.ν (μ : ℂ)) :=
    (hBR _ _ hL.regime hνn _ (hμ z hz)).2
  have hP := hpins z hz
  have hAN := (nearOpsAt_spec hP.near).1
  have hLj : ∀ T, affIota D.K.as (LjOp D.Pl D.K L μ T) =
      LjFun (cOf L.ν) D.K.mZ (L.ρb D.Pl D.K) (gRate D.Pl) L.ν L.ε μ D.K.χo D.K.χy T :=
    Classical.epsilon_spec hP.lj
  have hFA : ∀ A, (FAOp D.K L μ A : Chart → Merid) =ᵐ[srcMeasure (cOf L.ν)]
      FAcoef L.ν μ D.K.χf (affIota D.K.as A) := FAOp_spec hP.fA
  have hχf := hst.chiF
  have hD0' : IsUnit (nearOpsAt D.Pl D.K L μ).D0 := hD0 z hz
  have hS : NearInst.Kflat.IsFlatDuhamelColumn L.flat (cOf_pos L.ν_pos) L.train μ D.K.as D.K.χf :=
    hcol z hz
  set o := nearOpsAt D.Pl D.K L μ with ho
  set X : AffSp D.K.as →L[ℝ] AffSp D.K.as :=
    LjOp D.Pl D.K L μ ∘L o.flatColG (gRate D.Pl) L.ν_pos R0 ∘L FAOp D.K L μ with hXdef
  have hX : ∀ A, affIota D.K.as (X A) =
      KflatFun L.flat (cOf L.ν) L.ν L.ε μ D.K.χo D.K.χy D.K.χf (affIota D.K.as A) := by
    intro A
    rw [hXdef, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hLj]
    symm
    unfold KflatFun LjFun
    apply Lpt_congr_Xmt
    apply xmtCongr (cOf L.ν) L.ν L.ε μ D.K.χo D.K.χy D.K.hχo L.ν_pos
    set hh : Hsp (cOf L.ν) := (Real.sqrt Real.pi)⁻¹ • srcIso (cOf L.ν) (FAOp D.K L μ A)
      with hh_def
    have hhae : (hh : Chart → Merid) =ᵐ[ageμ (cOf L.ν) (-3 / 2)]
        NearInst.Kflat.affCoef L.ν μ D.K.χf (affIota D.K.as A) :=
      NearInst.Kflat.srcCoefAE (cOf L.ν) (FAOp D.K L μ A) _ (hFA A)
    obtain ⟨hMb, hb⟩ := NearInst.Kflat.flatColumn_solves o R0 hD0' hh
    set b : Hsp (cOf L.ν) := R0 hh - o.S0 (Ring.inverse o.D0 (o.M0 (R0 hh))) with hb_def
    have h1 := hS hχf D.K.mZ (L.ρb D.Pl D.K) o R0 hAN.flat hAN.free hR0 hD0' (affIota D.K.as A)
      (affIota_mem D.K.as A) hh b hhae hb
    have h2 : (((Ring.inverse o.D0 (o.M0 (R0 hh))).fst : Chart → Ten3)) =ᵐ[z1Measure (cOf L.ν) D.K.mZ]
        fun p => ten3Of (UnforcedLeray.Short.IIIa.symOuter (trainMer L.train p) (b p)) := by
      rw [← hMb]
      exact (hAN.flat b).1
    have h2' := (oldMeasureAC (cOf L.ν) D.K.mZ (gRate D.Pl) L.ν L.ν_pos).ae_le
      ((withDensity_absolutelyContinuous (z1Measure (cOf L.ν) D.K.mZ) _).ae_le h2)
    have h3 := (oldMeasureAC (cOf L.ν) D.K.mZ (gRate D.Pl) L.ν L.ν_pos).ae_le
      (NearInst.Kflat.thinFlatColG (cOf L.ν) D.K.mZ (L.ρb D.Pl D.K) (gRate D.Pl) L.ν L.ν_pos o R0
        (FAOp D.K L μ A))
    filter_upwards [h1, h2', h3] with p hp1 hp2 hp3
    rw [hp1, hp3, hp2]
    rfl
  have hKf : ∀ A, affIota D.K.as (KflatOp D.K L μ A) =
      KflatFun L.flat (cOf L.ν) L.ν L.ε μ D.K.χo D.K.χy D.K.χf (affIota D.K.as A) :=
    Classical.epsilon_spec (p := fun Kf : AffSp D.K.as →L[ℝ] AffSp D.K.as => ∀ A,
      affIota D.K.as (Kf A) =
        KflatFun L.flat (cOf L.ν) L.ν L.ε μ D.K.χo D.K.χy D.K.χf (affIota D.K.as A)) ⟨X, hX⟩
  exact hKf A

/-! ## 3. Assembly -/

/-- `A_* = ε³𝒜_ν` (source 4583, 5936-5940). -/
theorem ast_eq (D : SeqData) (n : ℕ) (z : ℝ) :
    retEps D.Pl D.σ₀ n ^ 3 * Anu D n z = Ast D n z := by
  rw [retEps_cube_eq]
  simp only [Anu, Ast, Astar, SeqData.mu]
  ring

/-- **`FlatNewtonComparison` from the three inputs** (source 4846-4907):
`‖𝒦^flatA - ℓ_μ(𝔗A)a_μ‖_𝒜 = ‖𝓛M - ℓ_μ(M)a_μ‖_𝒜 ≤ C₁ε³[N₁^χ(M) + ν^{-k}e^{-4a_s/(5ν)}N₀^χ(M)]
≤ C₁C₂A_*[ν + ν^{-k}e^{-4a_s/(5ν)}]‖A‖`, `M = 𝔗A`, on the window `K_σ₀` (`winK`). -/
theorem flatNewtonComparison_of (D : SeqData) (hU : FlatNearUnit D)
    (hN : ∀ (as : ℝ) (K : Set ℝ) (χo χy : ℝ → ℝ), NewtonTaylor as K χo χy)
    (hM : FrakTMoments D) : FlatNewtonComparison D := by
  intro dm dp hst hpin γ' _ _
  have hω := hst.omega_ne
  have hγ : 0 < D.Pl.eigenvalue.re := hst.gamma_pos
  have hσ0 := hst.sigma_pos
  have hσ1 := hst.sigma_lt
  obtain ⟨C₁, ν₀, k, hC₁, hν₀, H₁⟩ := hN D.K.as (NearInst.winK D.σ₀) D.K.χo D.K.χy hst.as_pos
    (NearInst.isCompact_winK _) (NearInst.winK_sub hσ0 hσ1)
  obtain ⟨C₂, N₂, hC₂, H₂⟩ := hM dm dp hst hpin
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 ((kflatPin_of D hU dm dp hst hpin).and
    ((D.eventually_lHyp hω hγ hσ0 hσ1 hst.chiY).and
      ((NearInst.eventually_mu_mem D hω hσ0 hσ1).and
        ((retNu_tendsto D.σ₀ hω).eventually (ge_mem_nhds hν₀)))))
  refine ⟨C₁ * C₂, k, max N₀ N₂, fun n hn z hz A => ?_⟩
  obtain ⟨hpinn, hLH, hμK, hνn⟩ := hN₀ n (le_trans (le_max_left _ _) hn)
  obtain ⟨hfin, hN1, hN0⟩ := H₂ n (le_trans (le_max_right _ _) hn) z hz A
  have hLHz := hLH z hz
  set ν : ℝ := nu D n with hνdef
  set μ : ℝ := D.mu n z with hμdef
  set ε : ℝ := retEps D.Pl D.σ₀ n with hεdef
  set M : Chart → Mat3 := frakT (D.flat n) ν μ D.K.χf (affIota D.K.as A) with hMdef
  set ℓ : ℝ := ellMuAt D n μ M with hℓdef
  have hν : 0 < ν := retNu_pos _ _ _
  have hμ0 : 0 < μ := hLHz.mu_pos
  have hε3 : 0 ≤ ε ^ 3 := pow_nonneg (retEps_pos D.coeff_ne n).le 3
  have hP : 0 ≤ ν⁻¹ ^ k * Real.exp (-(4 * D.K.as / 5) / ν) :=
    mul_nonneg (pow_nonneg (inv_nonneg.2 hν.le) _) (Real.exp_pos _).le
  have hPγ : 0 ≤ ν⁻¹ ^ k * Real.exp (-γ' / Real.sqrt ν) :=
    mul_nonneg (pow_nonneg (inv_nonneg.2 hν.le) _) (Real.exp_pos _).le
  have hA : 0 ≤ ‖A‖ := norm_nonneg _
  have hAnu : 0 ≤ Anu D n z := mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hν.le _)
  -- the function-level identity
  have hfun : affIota D.K.as (KflatOp D.K (D.level n) μ A - ℓ • aMuOp D.K μ) =
      Lpt (cOf ν) ν ε μ D.K.χo D.K.χy M -
        ellMuGen (cOf ν) ν ε μ D.K.χo M • aMuFun μ := by
    rw [map_sub, map_smul, hpinn z hz A, affIota_aMuOp hst.as_pos.le hμ0]
    rfl
  -- the kernel bound
  have hK : affNorm D.K.as (Lpt (cOf ν) ν ε μ D.K.χo D.K.χy M -
      ellMuGen (cOf ν) ν ε μ D.K.χo M • aMuFun μ) ≤
      C₁ * ε ^ 3 * (oldN1w (cOf ν) ν D.K.χo M +
        ν⁻¹ ^ k * Real.exp (-(4 * D.K.as / 5) / ν) * oldN0w (cOf ν) ν D.K.χo M) := by
    unfold affNorm
    refine csSup_le ((nonempty_Ioi (a := (0 : ℝ))).image _) ?_
    rintro _ ⟨s, hs, rfl⟩
    exact H₁ (cOf ν) ν ε μ hLHz hνn (hμK z hz) M hfin s hs
  rw [← affNorm_affIota, hfun]
  refine hK.trans ?_
  have hC1e : 0 ≤ C₁ * ε ^ 3 := mul_nonneg hC₁ hε3
  have hsum : oldN1w (cOf ν) ν D.K.χo M +
      ν⁻¹ ^ k * Real.exp (-(4 * D.K.as / 5) / ν) * oldN0w (cOf ν) ν D.K.χo M ≤
      C₂ * Anu D n z * ν * ‖A‖ +
        ν⁻¹ ^ k * Real.exp (-(4 * D.K.as / 5) / ν) * (C₂ * Anu D n z * ‖A‖) :=
    add_le_add hN1 (mul_le_mul_of_nonneg_left hN0 hP)
  have hast : ε ^ 3 * Anu D n z = Ast D n z := ast_eq D n z
  calc C₁ * ε ^ 3 * (oldN1w (cOf ν) ν D.K.χo M +
        ν⁻¹ ^ k * Real.exp (-(4 * D.K.as / 5) / ν) * oldN0w (cOf ν) ν D.K.χo M)
      ≤ C₁ * ε ^ 3 * (C₂ * Anu D n z * ν * ‖A‖ +
          ν⁻¹ ^ k * Real.exp (-(4 * D.K.as / 5) / ν) * (C₂ * Anu D n z * ‖A‖)) :=
        mul_le_mul_of_nonneg_left hsum hC1e
    _ = C₁ * C₂ * (ε ^ 3 * Anu D n z) *
          (ν + ν⁻¹ ^ k * Real.exp (-(4 * D.K.as / 5) / ν)) * ‖A‖ := by ring
    _ ≤ C₁ * C₂ * (ε ^ 3 * Anu D n z) * (ν + ν⁻¹ ^ k * Real.exp (-γ' / Real.sqrt ν) +
          ν⁻¹ ^ k * Real.exp (-(4 * D.K.as / 5) / ν)) * ‖A‖ := by
        apply mul_le_mul_of_nonneg_right _ hA
        apply mul_le_mul_of_nonneg_left _
          (mul_nonneg (mul_nonneg hC₁ hC₂) (mul_nonneg hε3 hAnu))
        linarith
    _ = C₁ * C₂ * Ast D n z * (ν + ν⁻¹ ^ k * Real.exp (-γ' / Real.sqrt ν) +
          ν⁻¹ ^ k * Real.exp (-(4 * D.K.as / 5) / ν)) * ‖A‖ := by rw [hast]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G5

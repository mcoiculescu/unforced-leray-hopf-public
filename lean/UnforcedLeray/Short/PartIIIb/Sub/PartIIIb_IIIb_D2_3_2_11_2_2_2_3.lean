import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_2_11_2_2_2

/-!
# `SepPhiMeasurableTop` decomposed (`PartIII-b:IIIb-D2/3/2/11/2/2/2/3`, source 3604-3621)

Source of record: `the November 2 reference manuscript`.
The integrand `Φ(l,z;τ,y) = -2 l^{2μ+2} ∇K_{ν(1-l²)}(y - l z) : T(τ + 2 log l, z)` of
`sep:resolvent` (3611-3617) is jointly `C^∞` in `((l,z),(τ,y))` for `l ∈ (0,1)` once `T` is
`C^∞` and `(t,x) ↦ K_t(x)` is jointly `C^∞` on `t > 0` (3604-3610: `K_t = δ G_t + ∂∂∫_t^∞ G_a`,
and by parabolic scaling `K_t(x) = t^{-3/2} K_1(x/√t)`).  Hence every partial derivative
`D^n_{(τ,y)} Φ` is continuous in `(l,z)` on `(0,1) × ℝ³`, which carries `sepRho`; continuity on a
full-measure measurable set gives `AEStronglyMeasurable`.

* `HeatLerayKJointSmoothTop`: joint smoothness of `(t,x) ↦ K_t(x)` on `t > 0`;
* `SepKernelFactorJointSmooth`: joint smoothness of `∂_k K_{ν(1-l²)}(y - l z)` on `l ∈ (0,1)`;
* `SepPhiJointSmoothTop`: joint smoothness of the integrand on `l ∈ (0,1)`;
* `contDiffAt_iteratedFDeriv_param` (proved here): partial iterated derivatives of a jointly
  smooth function are jointly smooth;
* `sepPhiMeasurableTop_of` (proved here): `SepPhiJointSmoothTop → SepPhiMeasurableTop`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- **Joint smoothness of the heat-Leray kernel** (source 3604-3610): `(t,x) ↦ (K_t)_{ij}(x)` is
`C^∞` near every `(t,x)` with `t > 0`.  (`K_t(x) = t^{-3/2} K_1(t^{-1/2} x)` by parabolic scaling,
`HeatLerayScale`, and `K_1` is `C^∞`, `HeatLerayKSmoothTop`.) -/
def HeatLerayKJointSmoothTop : Prop :=
  ∀ (i j : Fin 3) (q : ℝ × Space), 0 < q.1 →
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × Space => IIIa.heatLerayK q.1 i j q.2) q

/-- **Joint smoothness of the kernel factor** (source 3604-3617): for `l ∈ (0,1)` (so
`t = ν(1-l²) > 0`), `((l,z),(τ,y)) ↦ ∂_k (K_{ν(1-l²)})_{ij}(y - l z)` is `C^∞`
(parametric `fderiv` of the jointly smooth `(t,x) ↦ K_t(x)`, `ContDiffAt.fderiv`). -/
def SepKernelFactorJointSmooth : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ (i j k : Fin 3) (p x : ℝ × Space), p.1 ∈ Ioo (0 : ℝ) 1 →
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : (ℝ × Space) × (ℝ × Space) =>
        fderiv ℝ (fun w => IIIa.heatLerayK (ν * (1 - q.1.1 ^ 2)) i j w) (q.2.2 - q.1.1 • q.1.2)
          (coordinateVector k)) (p, x)

/-- **Joint smoothness of the `sep:resolvent` integrand** (source 3611-3617, with 3604-3610):
for `T` jointly `C^∞` and `l ∈ (0,1)`, `((l,z),(τ,y)) ↦ sepPhiJ ν μ T i (l,z) (τ,y)
= -2 l^{2μ+2} Σ_{jk} ∂_k(K_{ν(1-l²)})_{ij}(y - l z) T_{jk}(τ + 2 log l, z)` is `C^∞`
(`l ↦ l^{2μ+2}` and `l ↦ log l` are smooth on `l > 0`, `ν(1-l²) > 0`). -/
def SepPhiJointSmoothTop : Prop :=
  ∀ (ν : ℝ) (μ : ℂ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ), 0 < ν →
    (∀ j k : Fin 3, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => T x.1 x.2 j k)) →
    ∀ (i : Fin 3) (p x : ℝ × Space), p.1 ∈ Ioo (0 : ℝ) 1 →
      ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : (ℝ × Space) × (ℝ × Space) => sepPhiJ ν μ T i q.1 q.2) (p, x)

theorem sepTop_add_one_le : ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  exact_mod_cast (le_top : (⊤ : ℕ∞) + 1 ≤ ⊤)

/-- Partial iterated derivatives (in the second variable) of a function that is jointly `C^∞` at
`(e, x)` for every `x` are jointly `C^∞` at `(e, x)`. -/
theorem contDiffAt_iteratedFDeriv_param {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : E → F → G) (e : E)
    (hf : ∀ x : F, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry f) (e, x)) :
    ∀ (n : ℕ) (x : F), ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : E × F => iteratedFDeriv ℝ n (f q.1) q.2) (e, x) := by
  intro n
  induction n with
  | zero =>
    intro x
    have h0 : (fun q : E × F => iteratedFDeriv ℝ 0 (f q.1) q.2) =
        fun q => (continuousMultilinearCurryFin0 ℝ F G).symm (Function.uncurry f q) := by
      funext q
      rw [iteratedFDeriv_zero_eq_comp]
      rfl
    rw [h0]
    exact (continuousMultilinearCurryFin0 ℝ F G).symm.contDiff.contDiffAt.comp _ (hf x)
  | succ n ih =>
    intro x
    have h1 : (fun q : E × F => iteratedFDeriv ℝ (n + 1) (f q.1) q.2) =
        fun q => (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => F) G).symm
          (fderiv ℝ (fun w => iteratedFDeriv ℝ n (f q.1) w) q.2) := by
      funext q
      rw [iteratedFDeriv_succ_eq_comp_left]
      rfl
    rw [h1]
    refine ContDiffAt.continuousLinearMap_comp (𝕜 := ℝ) (E := E × F)
      (F := F →L[ℝ] F [×n]→L[ℝ] G) (G := F [×(n + 1)]→L[ℝ] G)
      (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => F) G).symm.toContinuousLinearEquiv.toContinuousLinearMap
      ?_
    have h2 : Function.uncurry (fun (q : E × F) (w : F) => iteratedFDeriv ℝ n (f q.1) w) =
        (fun q : E × F => iteratedFDeriv ℝ n (f q.1) q.2) ∘
          (fun r : (E × F) × F => (r.1.1, r.2)) := by
      funext r
      rfl
    have h3 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (Function.uncurry (fun (q : E × F) (w : F) => iteratedFDeriv ℝ n (f q.1) w))
        ((e, x), (e, x).2) := by
      rw [h2]
      exact ContDiffAt.comp (f := fun r : (E × F) × F => (r.1.1, r.2)) ((e, x), (e, x).2)
        (ih x) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
    exact ContDiffAt.fderiv (f := fun (q : E × F) (w : F) => iteratedFDeriv ℝ n (f q.1) w)
      (g := Prod.snd) h3 contDiffAt_snd sepTop_add_one_le

/-- `SepPhiMeasurableTop` from joint smoothness of the integrand: for each order `n` and each
`x = (τ,y)`, `p ↦ D^n_x Φ(p; x)` is continuous on `(0,1) × ℝ³`, a measurable set of full
`sepRho`-measure. -/
theorem sepPhiMeasurableTop_of (h : SepPhiJointSmoothTop) : SepPhiMeasurableTop := by
  intro ν μ P rOut T hν _hS hT i n x
  have hc : ContinuousOn (fun p : ℝ × Space => iteratedFDeriv ℝ n (sepPhiJ ν μ T i p) x)
      (Ioo (0 : ℝ) 1 ×ˢ univ) := by
    intro p hp
    have h1 := contDiffAt_iteratedFDeriv_param (fun p x => sepPhiJ ν μ T i p x) p
      (fun x => h ν μ T hν hT i p x hp.1) n x
    have h2 : ContinuousAt (fun p' : ℝ × Space => (p', x)) p :=
      (continuous_id.prodMk continuous_const).continuousAt
    exact (ContinuousAt.comp (g := fun q : (ℝ × Space) × (ℝ × Space) =>
      iteratedFDeriv ℝ n (sepPhiJ ν μ T i q.1) q.2) (f := fun p' : ℝ × Space => (p', x))
      h1.continuousAt h2).continuousWithinAt
  have hs : MeasurableSet (Ioo (0 : ℝ) 1 ×ˢ (univ : Set Space)) :=
    measurableSet_Ioo.prod MeasurableSet.univ
  have hr : sepRho.restrict (Ioo (0 : ℝ) 1 ×ˢ (univ : Set Space)) = sepRho := by
    apply Measure.restrict_eq_self_of_ae_mem
    filter_upwards [ae_mem_Ioo_sepRho] with p hp
    exact ⟨hp, mem_univ _⟩
  rw [← hr]
  exact hc.aestronglyMeasurable hs

end UnforcedLeray.Short.PartIIIb.Concrete

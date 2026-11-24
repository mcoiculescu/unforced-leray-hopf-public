import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F8_1_org_2_2

/-!
# Double-Heat-Regularized Volterra Oseen Evolution and Smooth `L²(C_c)` Derivative Tower

Support module 1 for task `PartII-b:F8/1/org/2/2` (`RealCylOseenMildSpatialBootstrap`).
Develops:
1. Iterated Gaussian heat-derivative operators `iterDHeatCLM hc α θ : L2v c →L[ℝ] L2v c`,
   iterated weak cell derivatives `HasIterWeakDeriv`, semigroup/commutation identities, and
   `L2v c`-norm age differentiability `(d/dθ) iterDHeatCLM hc α θ = Δ iterDHeatCLM hc α θ` (`θ > 0`).
2. Double-heat-regularized Oseen drift `bvRegCLM hc hV ε r = H_ε ∘ bvCLM r ∘ freeH1CLM ε` and
   associated `[0, 2]` Volterra evolution `E_oseenReg`, sharing the exact `ε`-independent Volterra
   constants `(M₀, C₀, β, lam, q, stripBound)` of `oseenVolterraData` and converging in `H1Sol c`
   on `[0, 2]` to `E_oseen` as `ε → 0⁺`.
3. Spatial derivative tower `uReg hc hν hV u₀ ε α t : L2v c` of `E_oseenReg` for `ε > 0`, `t ∈ (0, 2]`,
   its solenoidal and weak-derivative properties, and its exact `L2v c`-norm ODE on `(0, 2)`:
   `(d/dt) uReg ε α t = ν • (uReg ε (0::0::α) t + uReg ε (1::1::α) t) - P₀ (iterDHeatCLM α ε (f_ε t))`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.IIb.F8MildBoot

open UnforcedLeray
open UnforcedLeray.Short.IIb
open UnforcedLeray.Short.IIb.F8WeakEx
open UnforcedLeray.Cyl (L2v cellμ divFree P0 Vec2)
open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.HeatCylinder
open UnforcedLeray.B0284 (heatKernel2)
open UnforcedLeray.Infra.VolterraEvolution

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

/-! ## 1. Weak Cell Derivatives `HasWeakDeriv1`, `HasIterWeakDeriv`, and `iterDHeatCLM` -/

/-- First-order weak cell derivative `∂_j u = dx` in `L2v c`. -/
def HasWeakDeriv1 (c : ℝ) (j : Fin 2) (u dx : L2v c) : Prop :=
  ∀ k : Fin 2, F8Ex.HasWeakCellDerivR c j
    (fun y => (u : Plane → F8Ex.RMerid) y k)
    (fun y => (dx : Plane → F8Ex.RMerid) y k)

lemma hasWeakDeriv1_iff_inner {c : ℝ} (j : Fin 2) (u dx : L2v c) :
    HasWeakDeriv1 c j u dx ↔
      ∀ (ψ : Plane → ℝ) (hψ : B0579.IsCylTest c ψ) (k : Fin 2),
        ⟪u, cylSmoothToL2 (isCylSmooth_single (hψ.pd j) k)⟫_ℝ +
          ⟪dx, cylSmoothToL2 (isCylSmooth_single hψ k)⟫_ℝ = 0 :=
  hasWeakCellDerivR_l2_iff u dx j

lemma HasWeakDeriv1.unique {c : ℝ} (hc : 0 < c) {j : Fin 2} {u g₁ g₂ : L2v c}
    (h1 : HasWeakDeriv1 c j u g₁) (h2 : HasWeakDeriv1 c j u g₂) : g₁ = g₂ :=
  eq_of_hasWeakCellDerivR hc h1 h2

lemma HasWeakDeriv1.zero (c : ℝ) (j : Fin 2) : HasWeakDeriv1 c j 0 0 := by
  rw [hasWeakDeriv1_iff_inner]
  intro _ _ _
  simp

lemma HasWeakDeriv1.add {c : ℝ} {j : Fin 2} {u₁ dx₁ u₂ dx₂ : L2v c}
    (h1 : HasWeakDeriv1 c j u₁ dx₁) (h2 : HasWeakDeriv1 c j u₂ dx₂) :
    HasWeakDeriv1 c j (u₁ + u₂) (dx₁ + dx₂) := by
  rw [hasWeakDeriv1_iff_inner] at h1 h2 ⊢
  intro ψ hψ k
  rw [inner_add_left, inner_add_left]
  linarith [h1 ψ hψ k, h2 ψ hψ k]

lemma HasWeakDeriv1.sub {c : ℝ} {j : Fin 2} {u₁ dx₁ u₂ dx₂ : L2v c}
    (h1 : HasWeakDeriv1 c j u₁ dx₁) (h2 : HasWeakDeriv1 c j u₂ dx₂) :
    HasWeakDeriv1 c j (u₁ - u₂) (dx₁ - dx₂) := by
  rw [hasWeakDeriv1_iff_inner] at h1 h2 ⊢
  intro ψ hψ k
  rw [inner_sub_left, inner_sub_left]
  linarith [h1 ψ hψ k, h2 ψ hψ k]

lemma HasWeakDeriv1.smul {c : ℝ} {j : Fin 2} (r : ℝ) {u dx : L2v c}
    (h : HasWeakDeriv1 c j u dx) :
    HasWeakDeriv1 c j (r • u) (r • dx) := by
  rw [hasWeakDeriv1_iff_inner] at h ⊢
  intro ψ hψ k
  rw [real_inner_smul_left, real_inner_smul_left]
  linear_combination r * h ψ hψ k

lemma HasWeakDeriv1.intervalIntegral {c : ℝ} {j : Fin 2} {f df : ℝ → L2v c} {a b : ℝ}
    (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b)
    (hdf : IntervalIntegrable df volume a b)
    (h : ∀ r ∈ Icc a b, HasWeakDeriv1 c j (f r) (df r)) :
    HasWeakDeriv1 c j (∫ r in a..b, f r) (∫ r in a..b, df r) := by
  rw [hasWeakDeriv1_iff_inner]
  intro ψ hψ k
  set φ₁ := cylSmoothToL2 (isCylSmooth_single (hψ.pd j) k)
  set φ₀ := cylSmoothToL2 (isCylSmooth_single hψ k)
  have c1 : ⟪∫ r in a..b, f r, φ₁⟫_ℝ = ∫ r in a..b, ⟪f r, φ₁⟫_ℝ := by
    have hcomm := (innerSL ℝ φ₁).intervalIntegral_comp_comm hf
    change (∫ r in a..b, ⟪φ₁, f r⟫_ℝ) = ⟪φ₁, ∫ r in a..b, f r⟫_ℝ at hcomm
    rw [real_inner_comm, ← hcomm]
    exact intervalIntegral.integral_congr fun r _ => real_inner_comm (f r) φ₁
  have c2 : ⟪∫ r in a..b, df r, φ₀⟫_ℝ = ∫ r in a..b, ⟪df r, φ₀⟫_ℝ := by
    have hcomm := (innerSL ℝ φ₀).intervalIntegral_comp_comm hdf
    change (∫ r in a..b, ⟪φ₀, df r⟫_ℝ) = ⟪φ₀, ∫ r in a..b, df r⟫_ℝ at hcomm
    rw [real_inner_comm, ← hcomm]
    exact intervalIntegral.integral_congr fun r _ => real_inner_comm (df r) φ₀
  have hi1 : IntervalIntegrable (fun r => ⟪f r, φ₁⟫_ℝ) volume a b := by
    have hL : IntervalIntegrable (fun r => (innerSL ℝ φ₁) (f r)) volume a b :=
      ⟨(innerSL ℝ φ₁).integrable_comp hf.1, (innerSL ℝ φ₁).integrable_comp hf.2⟩
    exact hL.congr (fun r _ => real_inner_comm _ _)
  have hi2 : IntervalIntegrable (fun r => ⟪df r, φ₀⟫_ℝ) volume a b := by
    have hL : IntervalIntegrable (fun r => (innerSL ℝ φ₀) (df r)) volume a b :=
      ⟨(innerSL ℝ φ₀).integrable_comp hdf.1, (innerSL ℝ φ₀).integrable_comp hdf.2⟩
    exact hL.congr (fun r _ => real_inner_comm _ _)
  rw [c1, c2, ← intervalIntegral.integral_add hi1 hi2]
  have hz : ∀ r ∈ uIcc a b, ⟪f r, φ₁⟫_ℝ + ⟪df r, φ₀⟫_ℝ = 0 := by
    rw [uIcc_of_le hab]
    intro r hr
    exact (hasWeakDeriv1_iff_inner j (f r) (df r)).1 (h r hr) ψ hψ k
  rw [intervalIntegral.integral_congr hz, intervalIntegral.integral_zero]

lemma HasWeakDeriv1.centeredHeat {c : ℝ} (hc : 0 < c) (θ : ℝ) {j : Fin 2} {u dx : L2v c}
    (h : HasWeakDeriv1 c j u dx) :
    HasWeakDeriv1 c j (centeredHeatVecL2CLM hc θ u) (centeredHeatVecL2CLM hc θ dx) :=
  hasWeakCellDerivR_centeredHeatVecL2CLM hc θ h

/-- Uniqueness in `L2v c` from pairings against coordinate-single smooth cylinder tests. -/
lemma eq_of_inner_cylSmooth_single {c : ℝ} {z₁ z₂ : L2v c}
    (h : ∀ (ψ : Plane → ℝ) (hψ : B0579.IsCylTest c ψ) (k : Fin 2),
      ⟪z₁, cylSmoothToL2 (isCylSmooth_single hψ k)⟫_ℝ =
        ⟪z₂, cylSmoothToL2 (isCylSmooth_single hψ k)⟫_ℝ) :
    z₁ = z₂ := by
  have hcoord : ∀ k : Fin 2,
      (fun y => (z₁ : Plane → Vec2) y k - (z₂ : Plane → Vec2) y k) =ᵐ[(Sob.cylinder c).μ] 0 := by
    intro k
    let hpk : Vec2 →L[ℝ] ℝ := EuclideanSpace.proj k
    have hm1 : MemLp (fun y => (z₁ : Plane → Vec2) y k) 2 (Sob.cylinder c).μ := by
      rw [Cyl.cylinder_μ_eq]
      exact hpk.comp_memLp' (Lp.memLp z₁)
    have hm2 : MemLp (fun y => (z₂ : Plane → Vec2) y k) 2 (Sob.cylinder c).μ := by
      rw [Cyl.cylinder_μ_eq]
      exact hpk.comp_memLp' (Lp.memLp z₂)
    refine (Sob.cylinder c).ae_zero _ ((hm1.sub hm2).locallyIntegrable (by norm_num)) fun φ hφ => ?_
    have hφb : B0579.IsCylTest c φ := (isCylTest_sob_iff c φ).1 hφ
    have hsub : ⟪z₁ - z₂, cylSmoothToL2 (isCylSmooth_single hφb k)⟫_ℝ = 0 := by
      rw [inner_sub_left, h φ hφb k, sub_self]
    have hpair := inner_cylSmooth_single hφb k (z₁ - z₂)
    rw [hsub] at hpair
    rw [Cyl.cylinder_μ_eq]
    change ∫ y in Cyl.cell c, φ y * ((z₁ : Plane → Vec2) y k - (z₂ : Plane → Vec2) y k) = 0
    rw [← b0579_cell_eq_cyl_cell]
    have hae : (fun y => φ y * ((z₁ : Plane → Vec2) y k - (z₂ : Plane → Vec2) y k)) =ᵐ[F8Ex.cellMeas c]
        fun y => ((z₁ - z₂ : L2v c) : Plane → F8Ex.RMerid) y k * φ y := by
      have hcoe : ((z₁ - z₂ : L2v c) : Plane → Vec2) =ᵐ[F8Ex.cellMeas c]
          (z₁ : Plane → Vec2) - (z₂ : Plane → Vec2) := by
        rw [cellMeas_eq_cellμ]
        exact Lp.coeFn_sub z₁ z₂
      filter_upwards [hcoe] with y hy
      change φ y * (z₁ y k - z₂ y k) = ((z₁ - z₂ : L2v c) : Plane → Vec2) y k * φ y
      rw [hy]
      simp [mul_comm]
    exact (integral_congr_ae hae).trans hpair.symm
  apply Lp.ext
  have h0 := hcoord 0
  have h1 := hcoord 1
  rw [Cyl.cylinder_μ_eq] at h0 h1
  filter_upwards [h0, h1] with y hy0 hy1
  ext k
  fin_cases k
  · exact sub_eq_zero.mp hy0
  · exact sub_eq_zero.mp hy1

/-- Iterated weak cell derivative along a word `α : List (Fin 2)` (`[]` = identity,
`j :: α` = `∂_j` applied to the `α`-th derivative). -/
def HasIterWeakDeriv (c : ℝ) : List (Fin 2) → L2v c → L2v c → Prop
  | [], u, g => u = g
  | j :: α, u, g => ∃ h : L2v c, HasIterWeakDeriv c α u h ∧ HasWeakDeriv1 c j h g

lemma HasIterWeakDeriv.unique {c : ℝ} (hc : 0 < c) :
    ∀ {α : List (Fin 2)} {u g₁ g₂ : L2v c},
      HasIterWeakDeriv c α u g₁ → HasIterWeakDeriv c α u g₂ → g₁ = g₂
  | [], _, _, _, rfl, h2 => h2
  | _ :: _, _, _, _, ⟨_, hα1, hj1⟩, ⟨_, hα2, hj2⟩ => by
      obtain rfl := HasIterWeakDeriv.unique hc hα1 hα2
      exact hj1.unique hc hj2

lemma HasIterWeakDeriv.centeredHeat {c : ℝ} (hc : 0 < c) (θ : ℝ) :
    ∀ {α : List (Fin 2)} {u g : L2v c},
      HasIterWeakDeriv c α u g →
        HasIterWeakDeriv c α (centeredHeatVecL2CLM hc θ u) (centeredHeatVecL2CLM hc θ g)
  | [], _, _, rfl => rfl
  | _ :: _, _, _, ⟨h, hα, hj⟩ =>
      ⟨centeredHeatVecL2CLM hc θ h, hα.centeredHeat hc θ, hj.centeredHeat hc θ⟩

lemma HasIterWeakDeriv.append {c : ℝ} :
    ∀ {α β : List (Fin 2)} {u h g : L2v c},
      HasIterWeakDeriv c β u h → HasIterWeakDeriv c α h g →
        HasIterWeakDeriv c (α ++ β) u g
  | [], _, _, _, _, hβ, rfl => hβ
  | _ :: _, _, _, _, _, hβ, ⟨k, hα, hj⟩ => ⟨k, hβ.append hα, hj⟩

lemma HasIterWeakDeriv.to_sobWeakDeriv {c : ℝ} :
    ∀ {α : List (Fin 2)} {u g : L2v c},
      HasIterWeakDeriv c α u g →
        Sob.HasWeakDeriv (Sob.cylinder c) (α.map B0579.dir)
          (u : Plane → Vec2) (g : Plane → Vec2)
  | [], u, _, rfl =>
      Sob.HasWeakDeriv.nil fun _ hφ =>
        Sob.integrable_smul_of_memLp (Sob.CompactlyBounded.of_adm hφ)
          (TrainB.memLp_cell_to_weighted u)
  | j :: _, _, g, ⟨h, hα, hj⟩ =>
      (hα.to_sobWeakDeriv).cons ((hasWeakCellDerivR_of_vecH1 h g j).1 hj)

/-- Iterated partial derivative of a scalar function along `α : List (Fin 2)` in reverse order,
so `HasIterWeakDeriv c α u g` pairs against `ψ` via `(-1)^α.length` against `pdIterRev α ψ`. -/
def pdIterRev : List (Fin 2) → (Plane → ℝ) → (Plane → ℝ)
  | [], ψ => ψ
  | j :: α, ψ => pdIterRev α (B0579.pd j ψ)

lemma isCylTest_pdIterRev {c : ℝ} :
    ∀ (α : List (Fin 2)) {ψ : Plane → ℝ},
      B0579.IsCylTest c ψ → B0579.IsCylTest c (pdIterRev α ψ)
  | [], _, hψ => hψ
  | j :: α, _, hψ => isCylTest_pdIterRev α (hψ.pd j)

lemma HasIterWeakDeriv.inner_single {c : ℝ} :
    ∀ {α : List (Fin 2)} {u g : L2v c},
      HasIterWeakDeriv c α u g →
      ∀ (ψ : Plane → ℝ) (hψ : B0579.IsCylTest c ψ) (k : Fin 2),
        ⟪g, cylSmoothToL2 (isCylSmooth_single hψ k)⟫_ℝ =
          (-1 : ℝ) ^ α.length *
            ⟪u, cylSmoothToL2 (isCylSmooth_single (isCylTest_pdIterRev α hψ) k)⟫_ℝ
  | [], _, _, rfl, _, _, _ => by simp [pdIterRev]
  | j :: α, _, g, ⟨h, hα, hj⟩, ψ, hψ, k => by
      have h1 := (hasWeakDeriv1_iff_inner j h g).1 hj ψ hψ k
      have ih := hα.inner_single (B0579.pd j ψ) (hψ.pd j) k
      have hstep : ⟪g, cylSmoothToL2 (isCylSmooth_single hψ k)⟫_ℝ =
          -⟪h, cylSmoothToL2 (isCylSmooth_single (hψ.pd j) k)⟫_ℝ := by linarith
      rw [hstep, ih, List.length_cons, pow_succ]
      dsimp only [pdIterRev]
      ring

/-- Iterated Gaussian heat-derivative operator `D^α H_θ` on `L2v c`, splitting elapsed heat time
dyadically across derivatives. -/
def iterDHeatCLM {c : ℝ} (hc : 0 < c) : List (Fin 2) → ℝ → L2v c →L[ℝ] L2v c
  | [], θ => centeredHeatVecL2CLM hc θ
  | j :: α, θ => (DHeatCLM hc j (θ / 2)).comp (iterDHeatCLM hc α (θ / 2))

lemma iterDHeatCLM_P0_comm {c : ℝ} (hc : 0 < c) :
    ∀ (α : List (Fin 2)) (θ : ℝ) (x : L2v c),
      iterDHeatCLM hc α θ (P0 c x) = P0 c (iterDHeatCLM hc α θ x)
  | [], θ, x => centeredHeatVecL2CLM_P0_comm hc θ x
  | j :: α, θ, x => by
      simp only [iterDHeatCLM, ContinuousLinearMap.comp_apply]
      rw [iterDHeatCLM_P0_comm hc α (θ / 2) x, DHeatCLM_P0_comm hc j (θ / 2)]

private lemma iterDHeatCLM_weak_and_add {c : ℝ} (hc : 0 < c) :
    ∀ (α : List (Fin 2)),
      (∀ {θ : ℝ}, 0 < θ → ∀ x : L2v c,
        HasIterWeakDeriv c α (centeredHeatVecL2CLM hc θ x) (iterDHeatCLM hc α θ x)) ∧
      (∀ {θ₁ θ₂ : ℝ}, 0 < θ₁ → 0 < θ₂ → ∀ x : L2v c,
        iterDHeatCLM hc α (θ₁ + θ₂) x =
          centeredHeatVecL2CLM hc θ₁ (iterDHeatCLM hc α θ₂ x))
  | [] =>
      ⟨fun _ _ => rfl, fun {θ₁ θ₂} h1 h2 x => by
        have hcomp := centeredHeatVecL2CLM_comp_of_nonneg hc h1.le h2.le
        exact (congrArg (fun L : L2v c →L[ℝ] L2v c => L x) hcomp).symm⟩
  | j :: α => by
      obtain ⟨ih_weak, ih_add⟩ := iterDHeatCLM_weak_and_add hc α
      have hw : ∀ {θ : ℝ}, 0 < θ → ∀ x : L2v c,
          HasIterWeakDeriv c (j :: α) (centeredHeatVecL2CLM hc θ x)
            (iterDHeatCLM hc (j :: α) θ x) := by
        intro θ hθ x
        have h2 : 0 < θ / 2 := half_pos hθ
        refine ⟨iterDHeatCLM hc α θ x, ih_weak hθ x, ?_⟩
        have hsplit : iterDHeatCLM hc α θ x =
            centeredHeatVecL2CLM hc (θ / 2) (iterDHeatCLM hc α (θ / 2) x) := by
          have := ih_add h2 h2 x
          rwa [add_halves] at this
        rw [hsplit]
        exact hasWeakCellDerivR_DHeatCLM hc j h2 (iterDHeatCLM hc α (θ / 2) x)
      refine ⟨hw, fun {θ₁ θ₂} h1 h2 x => ?_⟩
      have hLHS := hw (add_pos h1 h2) x
      have hRHS : HasIterWeakDeriv c (j :: α) (centeredHeatVecL2CLM hc (θ₁ + θ₂) x)
          (centeredHeatVecL2CLM hc θ₁ (iterDHeatCLM hc (j :: α) θ₂ x)) := by
        have hcomp := congrArg (fun L : L2v c →L[ℝ] L2v c => L x)
          (centeredHeatVecL2CLM_comp_of_nonneg hc h1.le h2.le)
        dsimp only [ContinuousLinearMap.comp_apply] at hcomp
        rw [← hcomp]
        exact (hw h2 x).centeredHeat hc θ₁
      exact hLHS.unique hc hRHS

lemma hasIterWeakDeriv_iterDHeatCLM {c : ℝ} (hc : 0 < c) (α : List (Fin 2))
    {θ : ℝ} (hθ : 0 < θ) (x : L2v c) :
    HasIterWeakDeriv c α (centeredHeatVecL2CLM hc θ x) (iterDHeatCLM hc α θ x) :=
  (iterDHeatCLM_weak_and_add hc α).1 hθ x

lemma iterDHeatCLM_add_left {c : ℝ} (hc : 0 < c) (α : List (Fin 2))
    {θ₁ θ₂ : ℝ} (h1 : 0 < θ₁) (h2 : 0 < θ₂) (x : L2v c) :
    iterDHeatCLM hc α (θ₁ + θ₂) x =
      centeredHeatVecL2CLM hc θ₁ (iterDHeatCLM hc α θ₂ x) :=
  (iterDHeatCLM_weak_and_add hc α).2 h1 h2 x

lemma hasWeakDeriv1_iterDHeatCLM {c : ℝ} (hc : 0 < c) (j : Fin 2) (α : List (Fin 2))
    {θ : ℝ} (hθ : 0 < θ) (x : L2v c) :
    HasWeakDeriv1 c j (iterDHeatCLM hc α θ x) (iterDHeatCLM hc (j :: α) θ x) := by
  obtain ⟨h, hα, hj⟩ := hasIterWeakDeriv_iterDHeatCLM hc (j :: α) hθ x
  obtain rfl := (hasIterWeakDeriv_iterDHeatCLM hc α hθ x).unique hc hα
  exact hj

lemma iterDHeatCLM_singleton_eq {c : ℝ} (hc : 0 < c) (j : Fin 2) {θ : ℝ} (hθ : 0 < θ)
    (x : L2v c) :
    iterDHeatCLM hc [j] θ x = DHeatCLM hc j θ x :=
  (hasWeakDeriv1_iterDHeatCLM hc j [] hθ x).unique hc (hasWeakCellDerivR_DHeatCLM hc j hθ x)

lemma iterDHeatCLM_eq_centeredHeat_of_hasIterWeakDeriv {c : ℝ} (hc : 0 < c)
    {α : List (Fin 2)} {θ : ℝ} (hθ : 0 < θ) {x g : L2v c}
    (hg : HasIterWeakDeriv c α x g) :
    iterDHeatCLM hc α θ x = centeredHeatVecL2CLM hc θ g :=
  (hasIterWeakDeriv_iterDHeatCLM hc α hθ x).unique hc (hg.centeredHeat hc θ)

lemma iterDHeatCLM_comp {c : ℝ} (hc : 0 < c) (α β : List (Fin 2))
    {θ₁ θ₂ : ℝ} (h1 : 0 < θ₁) (h2 : 0 < θ₂) (x : L2v c) :
    iterDHeatCLM hc α θ₁ (iterDHeatCLM hc β θ₂ x) =
      iterDHeatCLM hc (α ++ β) (θ₁ + θ₂) x := by
  have hcomp : centeredHeatVecL2CLM hc θ₁ (centeredHeatVecL2CLM hc θ₂ x) =
      centeredHeatVecL2CLM hc (θ₁ + θ₂) x :=
    congrArg (fun L : L2v c →L[ℝ] L2v c => L x)
      (centeredHeatVecL2CLM_comp_of_nonneg hc h1.le h2.le)
  have hb : HasIterWeakDeriv c β (centeredHeatVecL2CLM hc (θ₁ + θ₂) x)
      (centeredHeatVecL2CLM hc θ₁ (iterDHeatCLM hc β θ₂ x)) := by
    rw [← hcomp]
    exact (hasIterWeakDeriv_iterDHeatCLM hc β h2 x).centeredHeat hc θ₁
  have ha := hasIterWeakDeriv_iterDHeatCLM hc α h1 (iterDHeatCLM hc β θ₂ x)
  exact (hb.append ha).unique hc (hasIterWeakDeriv_iterDHeatCLM hc (α ++ β) (add_pos h1 h2) x)

/-- Explicit operator-norm bound for `iterDHeatCLM hc α` at elapsed heat time `δ > 0`. -/
def iterDHeatBound : List (Fin 2) → ℝ → ℝ
  | [], _ => 1
  | _ :: α, δ => heatDivL2Coeff (δ / 2) * iterDHeatBound α (δ / 2)

lemma iterDHeatBound_nonneg :
    ∀ (α : List (Fin 2)) {δ : ℝ}, 0 < δ → 0 ≤ iterDHeatBound α δ
  | [], _, _ => zero_le_one
  | _ :: α, δ, hδ => by
      have h1 : 0 ≤ heatDivL2Coeff (δ / 2) := by
        unfold heatDivL2Coeff; positivity
      exact mul_nonneg h1 (iterDHeatBound_nonneg α (half_pos hδ))

lemma norm_iterDHeatCLM_at_le {c : ℝ} (hc : 0 < c) :
    ∀ (α : List (Fin 2)) {δ : ℝ}, 0 < δ → ‖iterDHeatCLM hc α δ‖ ≤ iterDHeatBound α δ
  | [], θ, _ => norm_centeredHeatVecL2CLM_le_one_all hc θ
  | j :: α, δ, hδ => by
      have h2 : 0 < δ / 2 := half_pos hδ
      calc ‖(DHeatCLM hc j (δ / 2)).comp (iterDHeatCLM hc α (δ / 2))‖
          ≤ ‖DHeatCLM hc j (δ / 2)‖ * ‖iterDHeatCLM hc α (δ / 2)‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ heatDivL2Coeff (δ / 2) * iterDHeatBound α (δ / 2) :=
            mul_le_mul (norm_DHeatCLM_le hc j h2) (norm_iterDHeatCLM_at_le hc α h2)
              (norm_nonneg _) (by unfold heatDivL2Coeff; positivity)

/-- Uniform operator-norm bound `‖iterDHeatCLM hc α θ‖ ≤ iterDHeatBound α δ` for all `θ ≥ δ > 0`. -/
lemma norm_iterDHeatCLM_le_of_ge {c : ℝ} (hc : 0 < c) (α : List (Fin 2))
    {δ θ : ℝ} (hδ : 0 < δ) (hδθ : δ ≤ θ) :
    ‖iterDHeatCLM hc α θ‖ ≤ iterDHeatBound α δ := by
  rcases eq_or_lt_of_le hδθ with rfl | hlt
  · exact norm_iterDHeatCLM_at_le hc α hδ
  · refine ContinuousLinearMap.opNorm_le_bound _ (iterDHeatBound_nonneg α hδ) fun x => ?_
    have heq : iterDHeatCLM hc α θ x =
        centeredHeatVecL2CLM hc (θ - δ) (iterDHeatCLM hc α δ x) := by
      have h := iterDHeatCLM_add_left hc α (sub_pos.mpr hlt) hδ x
      rwa [sub_add_cancel] at h
    rw [heq]
    calc ‖centeredHeatVecL2CLM hc (θ - δ) (iterDHeatCLM hc α δ x)‖
        ≤ 1 * ‖iterDHeatCLM hc α δ x‖ :=
          (ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul_of_nonneg_right
              (norm_centeredHeatVecL2CLM_le_one_all hc (θ - δ)) (norm_nonneg _))
      _ ≤ iterDHeatBound α δ * ‖x‖ := by
          rw [one_mul]
          exact (ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul_of_nonneg_right (norm_iterDHeatCLM_at_le hc α hδ) (norm_nonneg _))

/-- Norm-sense age derivative of `s ↦ centeredHeatVecL2CLM hc s y` in `L2v c` at `θ > 0`. -/
lemma hasDerivAt_centeredHeatVecL2CLM {c : ℝ} (hc : 0 < c) {θ : ℝ} (hθ : 0 < θ) (y : L2v c) :
    HasDerivAt (fun s : ℝ => centeredHeatVecL2CLM hc s y)
      (iterDHeatCLM hc [0, 0] θ y + iterDHeatCLM hc [1, 1] θ y) θ := by
  let F : ℝ → Plane → L2v c := fun s w => heatKernel2 s w • planeShiftL2CLM hc w y
  let F' : ℝ → Plane → L2v c := fun s w => heatKernel2AgeDerivative s w • planeShiftL2CLM hc w y
  have hball : Ioo (θ / 2) (2 * θ) ∈ 𝓝 θ := Ioo_mem_nhds (by linarith) (by linarith)
  have hwide : Integrable (fun w : Plane => (1 + w.1 ^ 2 + w.2 ^ 2) * heatKernel2 (2 * θ) w) :=
    integrable_one_add_sq_mul_heatKernel2 (by positivity)
  let A : ℝ := 4 * (θ⁻¹ ^ 2 + 2 / θ)
  have hdomInt : Integrable
      (fun w : Plane => A * ‖y‖ * ((1 + w.1 ^ 2 + w.2 ^ 2) * heatKernel2 (2 * θ) w)) :=
    hwide.const_mul (A * ‖y‖)
  have horb : Continuous (fun w : Plane => planeShiftL2CLM hc w y) :=
    continuous_planeShiftL2_orbit hc y
  have hFmeas : ∀ᶠ s : ℝ in 𝓝 θ, AEStronglyMeasurable (F s) volume := by
    filter_upwards [] with s
    have hk : Continuous (heatKernel2 s) := by
      unfold B0284.heatKernel2 B0191.heatKernel; fun_prop
    exact hk.aestronglyMeasurable.smul horb.aestronglyMeasurable
  have hFint : Integrable (F θ) volume :=
    integrable_kernel_smul_planeShift hc (B0284.integrable_heatKernel2 hθ) y
  have hFprimeMeas : AEStronglyMeasurable (F' θ) volume := by
    have hk : Measurable (heatKernel2AgeDerivative θ) := by
      unfold heatKernel2AgeDerivative B0284.heatKernel2 B0191.heatKernel; fun_prop
    exact hk.aestronglyMeasurable.smul horb.aestronglyMeasurable
  have hFprimeBound : ∀ᵐ w ∂(volume : Measure Plane), ∀ s ∈ Ioo (θ / 2) (2 * θ),
      ‖F' s w‖ ≤ A * ‖y‖ * ((1 + w.1 ^ 2 + w.2 ^ 2) * heatKernel2 (2 * θ) w) := by
    filter_upwards [] with w s hs
    have hloc := abs_heatKernel2AgeDerivative_le_local (θ₀ := θ) hθ hs.1 hs.2 w
    dsimp only [F', A]
    rw [norm_smul, Real.norm_eq_abs, norm_planeShiftL2CLM hc w y]
    calc |heatKernel2AgeDerivative s w| * ‖y‖
        ≤ (4 * (θ⁻¹ ^ 2 + 2 / θ) * ((1 + w.1 ^ 2 + w.2 ^ 2) * heatKernel2 (2 * θ) w)) * ‖y‖ :=
          mul_le_mul_of_nonneg_right hloc (norm_nonneg _)
      _ = 4 * (θ⁻¹ ^ 2 + 2 / θ) * ‖y‖ * ((1 + w.1 ^ 2 + w.2 ^ 2) * heatKernel2 (2 * θ) w) := by
          ring
  have hdiff : ∀ᵐ w ∂(volume : Measure Plane), ∀ s ∈ Ioo (θ / 2) (2 * θ),
      HasDerivAt (F · w) (F' s w) s := by
    filter_upwards [] with w s hs
    have hpos : 0 < s := lt_trans (by positivity) hs.1
    exact (hasDerivAt_heatKernel2_age hpos w).smul_const (planeShiftL2CLM hc w y)
  have hparam := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure Plane)) (F := F) (F' := F')
    (bound := fun w => A * ‖y‖ * ((1 + w.1 ^ 2 + w.2 ^ 2) * heatKernel2 (2 * θ) w))
    hball hFmeas hFint hFprimeMeas hFprimeBound hdomInt hdiff).2
  have hev : (fun s : ℝ => ∫ w : Plane, F s w) =ᶠ[𝓝 θ]
      fun s => centeredHeatVecL2CLM hc s y := by
    filter_upwards [Ioi_mem_nhds hθ] with s hs
    exact (centeredHeat_eq_shiftAvgCLM hc hs y).symm
  have hd_norm : HasDerivAt (fun s : ℝ => centeredHeatVecL2CLM hc s y)
      (∫ w : Plane, F' θ w) θ := hparam.congr_of_eventuallyEq hev.symm
  have h_eq : (∫ w : Plane, F' θ w) =
      iterDHeatCLM hc [0, 0] θ y + iterDHeatCLM hc [1, 1] θ y := by
    refine eq_of_inner_cylSmooth_single fun ψ hψ k => ?_
    set hΦ := isCylSmooth_single hψ k
    set φ₀ := cylSmoothToL2 hΦ
    have hd1 : HasDerivAt (fun s : ℝ => ⟪φ₀, centeredHeatVecL2CLM hc s y⟫_ℝ)
        ⟪φ₀, ∫ w : Plane, F' θ w⟫_ℝ θ :=
      (innerSL ℝ φ₀).hasFDerivAt.comp_hasDerivAt θ hd_norm
    have hd2 := hasDerivAt_inner_centeredHeatVecL2CLM hc hθ hΦ y
    have hpair_eq := hd1.unique hd2
    have hibp : ∀ j : Fin 2,
        -⟪cylSmoothToL2 (hΦ.dir (B0579.dir j)), DHeatCLM hc j θ y⟫_ℝ =
          ⟪φ₀, iterDHeatCLM hc [j, j] θ y⟫_ℝ := by
      intro j
      have hdir : (fun z => fderiv ℝ (fun x => ψ x • EuclideanSpace.single k (1 : ℝ)) z
          (B0579.dir j)) = fun z => B0579.pd j ψ z • EuclideanSpace.single k (1 : ℝ) := by
        funext z
        rw [fderiv_smul_const (hψ.differentiable z)]
        rfl
      have htoLp : cylSmoothToL2 (hΦ.dir (B0579.dir j)) =
          cylSmoothToL2 (isCylSmooth_single (hψ.pd j) k) := by
        apply Lp.ext
        filter_upwards [(memLp_of_cylSmooth (hΦ.dir (B0579.dir j))).coeFn_toLp,
          (memLp_of_cylSmooth (isCylSmooth_single (hψ.pd j) k)).coeFn_toLp] with z h1 h2
        exact h1.trans ((congrFun hdir z).trans h2.symm)
      have hwj : HasWeakDeriv1 c j (DHeatCLM hc j θ y) (iterDHeatCLM hc [j, j] θ y) := by
        rw [← iterDHeatCLM_singleton_eq hc j hθ y]
        exact hasWeakDeriv1_iterDHeatCLM hc j [j] hθ y
      have hk := (hasWeakDeriv1_iff_inner j (DHeatCLM hc j θ y)
        (iterDHeatCLM hc [j, j] θ y)).1 hwj ψ hψ k
      rw [htoLp]
      linarith [hk,
        real_inner_comm (DHeatCLM hc j θ y) (cylSmoothToL2 (isCylSmooth_single (hψ.pd j) k)),
        real_inner_comm φ₀ (iterDHeatCLM hc [j, j] θ y)]
    have h0 := hibp 0
    have h1 := hibp 1
    have hd0 : B0579.dir 0 = ((1 : ℝ), (0 : ℝ)) := rfl
    have hd1' : B0579.dir 1 = ((0 : ℝ), (1 : ℝ)) := rfl
    rw [hd0] at h0
    rw [hd1'] at h1
    rw [real_inner_comm φ₀, hpair_eq, real_inner_comm φ₀, inner_add_right]
    linarith [h0, h1]
  rwa [h_eq] at hd_norm

/-- Norm-sense age derivative of `s ↦ iterDHeatCLM hc α s x` in `L2v c` at `θ > 0`. -/
lemma hasDerivAt_iterDHeatCLM {c : ℝ} (hc : 0 < c) (α : List (Fin 2))
    {θ : ℝ} (hθ : 0 < θ) (x : L2v c) :
    HasDerivAt (fun s : ℝ => iterDHeatCLM hc α s x)
      (iterDHeatCLM hc (0 :: 0 :: α) θ x + iterDHeatCLM hc (1 :: 1 :: α) θ x) θ := by
  have h2 : 0 < θ / 2 := half_pos hθ
  set y := iterDHeatCLM hc α (θ / 2) x
  have hd_sub : HasDerivAt (fun s : ℝ => s - θ / 2) 1 θ := by
    simpa using (hasDerivAt_id θ).sub_const (θ / 2)
  have hd_comp :=
    (hasDerivAt_centeredHeatVecL2CLM hc (by linarith : 0 < θ - θ / 2) y).scomp θ hd_sub
  have hev : (fun s : ℝ => iterDHeatCLM hc α s x) =ᶠ[𝓝 θ]
      ((fun u : ℝ => centeredHeatVecL2CLM hc u y) ∘ fun s : ℝ => s - θ / 2) := by
    filter_upwards [Ioi_mem_nhds (half_lt_self hθ)] with s hs
    dsimp only [Function.comp_apply]
    have hs_pos : 0 < s - θ / 2 := sub_pos.mpr hs
    have h := iterDHeatCLM_add_left hc α hs_pos h2 x
    rwa [sub_add_cancel] at h
  have hsub_half : θ - θ / 2 = θ / 2 := by ring
  have hc0 : iterDHeatCLM hc [0, 0] (θ / 2) y = iterDHeatCLM hc (0 :: 0 :: α) θ x := by
    have h := iterDHeatCLM_comp hc [0, 0] α h2 h2 x
    simpa [add_halves] using h
  have hc1 : iterDHeatCLM hc [1, 1] (θ / 2) y = iterDHeatCLM hc (1 :: 1 :: α) θ x := by
    have h := iterDHeatCLM_comp hc [1, 1] α h2 h2 x
    simpa [add_halves] using h
  rw [one_smul, hsub_half, hc0, hc1] at hd_comp
  exact hd_comp.congr_of_eventuallyEq hev

/-! ## 2. Double-Heat-Regularized Volterra Evolution `E_oseenReg` and `ε → 0⁺` Convergence -/

/-- Double-heat-regularized Oseen drift operator `H_ε ∘ bvCLM r ∘ freeH1CLM ε`. -/
def bvRegCLM {c : ℝ} (hc : 0 < c) {V : ℝ → Plane → F8Ex.RMerid}
    (hV : F8Ex.IsSmoothBUCDrift c V) (ε r : ℝ) : H1Sol c →L[ℝ] L2v c :=
  (centeredHeatVecL2CLM hc ε).comp ((bvCLM hc hV r).comp (freeH1CLM hc ε))

lemma norm_bvRegCLM_le {c : ℝ} (hc : 0 < c) {V : ℝ → Plane → F8Ex.RMerid}
    (hV : F8Ex.IsSmoothBUCDrift c V) (ε r : ℝ) :
    ‖bvRegCLM hc hV ε r‖ ≤ 6 * driftBound hV := by
  have hdb : 0 ≤ 6 * driftBound hV :=
    (norm_nonneg (bvCLM hc hV r)).trans (norm_bvCLM_le hc hV r)
  calc ‖(centeredHeatVecL2CLM hc ε).comp ((bvCLM hc hV r).comp (freeH1CLM hc ε))‖
      ≤ ‖centeredHeatVecL2CLM hc ε‖ * ‖(bvCLM hc hV r).comp (freeH1CLM hc ε)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (‖bvCLM hc hV r‖ * ‖freeH1CLM hc ε‖) :=
        mul_le_mul (norm_centeredHeatVecL2CLM_le_one_all hc ε)
          (ContinuousLinearMap.opNorm_comp_le _ _)
          (norm_nonneg ((bvCLM hc hV r).comp (freeH1CLM hc ε))) zero_le_one
    _ ≤ 1 * ((6 * driftBound hV) * 1) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul (norm_bvCLM_le hc hV r) (norm_freeH1CLM_le hc ε)
            (norm_nonneg (freeH1CLM hc ε)) hdb) zero_le_one
    _ = 6 * driftBound hV := by ring

lemma continuous_bvRegCLM_apply {c : ℝ} (hc : 0 < c) {V : ℝ → Plane → F8Ex.RMerid}
    (hV : F8Ex.IsSmoothBUCDrift c V) (ε : ℝ) (p : H1Sol c) :
    Continuous (fun r : ℝ => bvRegCLM hc hV ε r p) :=
  (centeredHeatVecL2CLM hc ε).continuous.comp
    (continuous_bvCLM_apply hc hV (freeH1CLM hc ε p))

/-- Double-heat-regularized Volterra data on `[0, 1]` with identical `(M₀, C₀, β)` constants to
`oseenVolterraData`. -/
def oseenRegVolterraData {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν) {V : ℝ → Plane → F8Ex.RMerid}
    (hV : F8Ex.IsSmoothBUCDrift c V) (ε : ℝ) : VolterraData ℝ (H1Sol c) (L2v c) where
  S₀ := (oseenVolterraData hc hν hV).S₀
  S := (oseenVolterraData hc hν hV).S
  B σ := bvRegCLM hc hV ε (2 * σ)
  M₀ := (oseenVolterraData hc hν hV).M₀
  C₀ := (oseenVolterraData hc hν hV).C₀
  β := (oseenVolterraData hc hν hV).β
  norm_S₀_le := (oseenVolterraData hc hν hV).norm_S₀_le
  norm_S_le := (oseenVolterraData hc hν hV).norm_S_le
  norm_B_le σ := norm_bvRegCLM_le hc hV ε (2 * σ)
  continuousOn_S₀ := (oseenVolterraData hc hν hV).continuousOn_S₀
  continuousOn_S := (oseenVolterraData hc hν hV).continuousOn_S
  continuous_B p :=
    (continuous_bvRegCLM_apply hc hV ε p).comp (continuous_const.mul continuous_id)

/-- Rescaled `[0, 2]` evolution operator of `oseenRegVolterraData`. -/
def E_oseenReg {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν) {V : ℝ → Plane → F8Ex.RMerid}
    (hV : F8Ex.IsSmoothBUCDrift c V) (ε t a : ℝ) : H1Sol c →L[ℝ] H1Sol c :=
  (oseenRegVolterraData hc hν hV ε).stripEvolution (t / 2) (a / 2)

/-- Uniform `ε`-independent `H1Sol c` norm bound on `E_oseenReg`. -/
lemma norm_E_oseenReg_le {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν) {V : ℝ → Plane → F8Ex.RMerid}
    (hV : F8Ex.IsSmoothBUCDrift c V) (ε t a : ℝ) (u₀ : H1Sol c) :
    ‖E_oseenReg hc hν hV ε t a u₀‖ ≤
      (oseenVolterraData hc hν hV).stripBound * ‖u₀‖ := by
  have hsb : (oseenRegVolterraData hc hν hV ε).stripBound =
      (oseenVolterraData hc hν hV).stripBound := rfl
  calc ‖E_oseenReg hc hν hV ε t a u₀‖
      ≤ ‖E_oseenReg hc hν hV ε t a‖ * ‖u₀‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ (oseenRegVolterraData hc hν hV ε).stripBound * ‖u₀‖ :=
        mul_le_mul_of_nonneg_right
          ((oseenRegVolterraData hc hν hV ε).norm_stripEvolution_le (t / 2) (a / 2))
          (norm_nonneg _)
    _ = (oseenVolterraData hc hν hV).stripBound * ‖u₀‖ := by rw [hsb]

lemma continuousOn_E_oseenReg {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν) {V : ℝ → Plane → F8Ex.RMerid}
    (hV : F8Ex.IsSmoothBUCDrift c V) (ε : ℝ) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 2) (x : H1Sol c) :
    ContinuousOn (fun t => E_oseenReg hc hν hV ε t a x) (Icc a 2) := by
  refine ((oseenRegVolterraData hc hν hV ε).continuousOn_stripEvolution (a / 2) x).comp
    (continuousOn_id.div_const 2) ?_
  intro t ht
  exact ⟨by linarith [ht.1], by linarith [ht.2, ha.1]⟩

private lemma stripEvolution_div_two_zero {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D : VolterraData ℝ E F) {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t ≤ 2) (x : E) :
    IntervalIntegrable
      (fun r => (-2⁻¹ : ℝ) • D.S (t / 2 - r / 2) (D.B (r / 2) (D.stripEvolution (r / 2) 0 x)))
      volume 0 t ∧
    D.stripEvolution (t / 2) 0 x = D.S₀ (t / 2 - 0) x -
      ∫ r in (0 : ℝ)..t, (-2⁻¹ : ℝ) •
        D.S (t / 2 - r / 2) (D.B (r / 2) (D.stripEvolution (r / 2) 0 x)) := by
  let g : ℝ → E := fun σ => D.S (t / 2 - σ) (D.B σ (D.stripEvolution σ 0 x))
  have hτ : t / 2 ∈ Icc (0 : ℝ) (0 + 1) := ⟨by linarith, by linarith⟩
  have hcs : ContinuousOn (fun σ => D.stripEvolution σ 0 x) (Icc 0 (t / 2)) :=
    (D.continuousOn_stripEvolution 0 x).mono (Icc_subset_Icc_right hτ.2)
  have hint_σ : IntervalIntegrable g volume 0 (t / 2) :=
    D.intervalIntegrable_integrand hτ.1 hτ.2 hcs
  have hint_mul : IntervalIntegrable (fun r => g (2⁻¹ * r)) volume 0 t := by
    have h1 := hint_σ.comp_mul_left (c := (2⁻¹ : ℝ)) enorm_ne_top enorm_ne_top
    have ha' : (0 : ℝ) / (2⁻¹ : ℝ) = 0 := by ring
    have ht' : (t / 2) / (2⁻¹ : ℝ) = t := by ring
    rwa [ha', ht'] at h1
  have hdiv_eq : (fun r : ℝ => (-2⁻¹ : ℝ) • g (r / 2)) =
      fun r => (-2⁻¹ : ℝ) • g (2⁻¹ * r) := by
    funext r; congr 2; ring
  have hint_r : IntervalIntegrable (fun r => (-2⁻¹ : ℝ) • g (r / 2)) volume 0 t := by
    rw [hdiv_eq]
    exact hint_mul.smul (-2⁻¹ : ℝ)
  refine ⟨hint_r, ?_⟩
  have heq := D.stripEvolution_eq hτ x
  have hchg := intervalIntegral.integral_comp_div g (a := 0) (b := t) (c := (2 : ℝ)) (by norm_num)
  have h0 : (0 : ℝ) / 2 = 0 := by norm_num
  have hc2 : (-2⁻¹ : ℝ) * (2 : ℝ) = -1 := by norm_num
  have hduhamel : (∫ r in (0 : ℝ)..t, (-2⁻¹ : ℝ) • g (r / 2)) =
      -(∫ σ in (0 : ℝ)..(t / 2), g σ) := by
    rw [intervalIntegral.integral_smul, hchg, h0, smul_smul, hc2, neg_one_smul]
  rw [heq, hduhamel, sub_neg_eq_add]

lemma E_oseenReg_mild {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν) {V : ℝ → Plane → F8Ex.RMerid}
    (hV : F8Ex.IsSmoothBUCDrift c V) (ε : ℝ) {t : ℝ}
    (ht0 : 0 ≤ t) (ht2 : t ≤ 2) (x : H1Sol c) :
    IntervalIntegrable
      (fun r => duhH1CLM hc (ν * (t - r))
        (bvRegCLM hc hV ε r (E_oseenReg hc hν hV ε r 0 x)))
      volume 0 t ∧
    E_oseenReg hc hν hV ε t 0 x = freeH1CLM hc (ν * t) x -
      ∫ r in (0 : ℝ)..t, duhH1CLM hc (ν * (t - r))
        (bvRegCLM hc hV ε r (E_oseenReg hc hν hV ε r 0 x)) := by
  obtain ⟨hint, heq⟩ :=
    stripEvolution_div_two_zero (oseenRegVolterraData hc hν hV ε) ht0 ht2 x
  have h0 : (0 : ℝ) / 2 = 0 := by norm_num
  have hc1 : (-2⁻¹ : ℝ) * (-2 : ℝ) = 1 := by norm_num
  have hS0_arg : 2 * ν * (t / 2 - 0) = ν * t := by ring
  have hS0_eq : (oseenRegVolterraData hc hν hV ε).S₀ (t / 2 - 0) x =
      freeH1CLM hc (ν * t) x := by
    change freeH1CLM hc (2 * ν * (t / 2 - 0)) x = _
    rw [hS0_arg]
  have hterm : (fun r => (-2⁻¹ : ℝ) •
      (oseenRegVolterraData hc hν hV ε).S (t / 2 - r / 2)
        ((oseenRegVolterraData hc hν hV ε).B (r / 2)
          ((oseenRegVolterraData hc hν hV ε).stripEvolution (r / 2) 0 x))) =
      fun r => duhH1CLM hc (ν * (t - r))
        (bvRegCLM hc hV ε r (E_oseenReg hc hν hV ε r 0 x)) := by
    funext r
    have h1 : 2 * ν * (t / 2 - r / 2) = ν * (t - r) := by ring
    have h2 : 2 * (r / 2) = r := by ring
    let y : H1Sol c := (oseenRegVolterraData hc hν hV ε).stripEvolution (r / 2) 0 x
    have hy : E_oseenReg hc hν hV ε r 0 x = y := by
      unfold E_oseenReg
      rw [h0]
    change (-2⁻¹ : ℝ) • (((-2 : ℝ) • duhH1CLM hc (2 * ν * (t / 2 - r / 2)))
        (bvRegCLM hc hV ε (2 * (r / 2)) y)) =
      duhH1CLM hc (ν * (t - r)) (bvRegCLM hc hV ε r (E_oseenReg hc hν hV ε r 0 x))
    rw [hy, h1, h2, smul_apply, smul_smul, hc1, one_smul]
  rw [hterm] at hint heq
  refine ⟨hint, ?_⟩
  have hEt : E_oseenReg hc hν hV ε t 0 x =
      (oseenRegVolterraData hc hν hV ε).stripEvolution (t / 2) 0 x := by
    unfold E_oseenReg
    rw [h0]
  rw [hEt, heq, hS0_eq]

/-- Uniform convergence on a compact set for a family of contractions converging strongly at `0`. -/
private lemma eventually_uniform_contraction_on_Icc {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : ℝ → E →L[ℝ] E} (hT_norm : ∀ ε, ‖T ε‖ ≤ 1)
    (hT_lim : ∀ x : E, Tendsto (fun ε => T ε x) (𝓝 0) (𝓝 x))
    {γ : ℝ → E} (hγ : ContinuousOn γ (Icc (0 : ℝ) 1))
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ ε : ℝ in 𝓝 0, ∀ σ ∈ Icc (0 : ℝ) 1, ‖T ε (γ σ) - γ σ‖ < δ := by
  have hK : IsCompact (γ '' Icc (0 : ℝ) 1) := isCompact_Icc.image_of_continuousOn hγ
  have hcov : ∀ x ∈ γ '' Icc (0 : ℝ) 1, Metric.ball x (δ / 3) ∈ 𝓝 x :=
    fun x _ => Metric.ball_mem_nhds x (by linarith)
  obtain ⟨s, _, hs_cov⟩ := hK.elim_nhds_subcover (fun x => Metric.ball x (δ / 3)) hcov
  have hev_s : ∀ᶠ ε : ℝ in 𝓝 0, ∀ x ∈ s, ‖T ε x - x‖ < δ / 3 := by
    rw [Finset.eventually_all]
    intro x _
    exact (tendsto_iff_norm_sub_tendsto_zero.mp (hT_lim x)).eventually (gt_mem_nhds (by linarith))
  filter_upwards [hev_s] with ε hε σ hσ
  have hmem : γ σ ∈ ⋃ x ∈ s, Metric.ball x (δ / 3) := hs_cov (mem_image_of_mem γ hσ)
  rw [mem_iUnion₂] at hmem
  obtain ⟨x, hxs, hx_dist⟩ := hmem
  rw [Metric.mem_ball, dist_eq_norm] at hx_dist
  have htri : T ε (γ σ) - γ σ = T ε (γ σ - x) + (T ε x - x) - (γ σ - x) := by
    rw [map_sub]
    abel
  have h1 : ‖T ε (γ σ - x)‖ ≤ ‖γ σ - x‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_of_le_one_left (norm_nonneg _) (hT_norm ε))
  calc ‖T ε (γ σ) - γ σ‖
      = ‖T ε (γ σ - x) + (T ε x - x) - (γ σ - x)‖ := by rw [htri]
    _ ≤ ‖T ε (γ σ - x) + (T ε x - x)‖ + ‖γ σ - x‖ := norm_sub_le _ _
    _ ≤ ‖T ε (γ σ - x)‖ + ‖T ε x - x‖ + ‖γ σ - x‖ :=
        add_le_add (norm_add_le _ _) le_rfl
    _ < δ / 3 + δ / 3 + δ / 3 := by linarith [hε x hxs]
    _ = δ := by ring

/-- Abstract Volterra perturbation stability on `[0, 1]` when two `VolterraData` structures share
`(S₀, S, C₀, β, lam, q)` and their drift operators differ by at most `η` along the unperturbed
orbit `σ ↦ D₀.stripEvolution σ 0 x`. -/
private lemma norm_stripEvolution_sub_le_of_B_err {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D₀ D₁ : VolterraData ℝ E F)
    (hS₀ : D₁.S₀ = D₀.S₀) (hS : D₁.S = D₀.S)
    (hC₀ : D₁.C₀ = D₀.C₀) (hβ : D₁.β = D₀.β)
    (hlam : D₁.lam = D₀.lam) (_hq : D₁.q = D₀.q)
    (x : E) {η : ℝ} (hη : 0 ≤ η)
    (hB_err : ∀ σ ∈ Icc (0 : ℝ) 1,
      ‖D₁.B σ (D₀.stripEvolution σ 0 x) - D₀.B σ (D₀.stripEvolution σ 0 x)‖ ≤ η)
    {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) :
    ‖D₁.stripEvolution τ 0 x - D₀.stripEvolution τ 0 x‖ ≤
      (4 * D₀.C₀ * Real.exp D₀.lam) * η := by
  let u : ℝ → E := fun σ => D₀.stripEvolution σ 0 x
  let u₁ : ℝ → E := fun σ => D₁.stripEvolution σ 0 x
  have hu_cont : ContinuousOn u (Icc 0 1) := by
    simpa using D₀.continuousOn_stripEvolution 0 x
  have hu₁_cont : ContinuousOn u₁ (Icc 0 1) := by
    simpa using D₁.continuousOn_stripEvolution 0 x
  have hC₀_nn : 0 ≤ D₀.C₀ := D₀.C₀_nonneg
  let w : ℝ → E := fun σ => u₁ σ - u σ
  let W : ℝ → ℝ := fun σ => Real.exp (-D₀.lam * σ) * ‖w σ‖
  have hW_cont : ContinuousOn W (Icc 0 1) :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).mul
      (continuous_norm.comp_continuousOn (hu₁_cont.sub hu_cont))
  obtain ⟨τ₀, hτ₀, hτ₀_max⟩ :=
    isCompact_Icc.exists_isMaxOn ⟨0, left_mem_Icc.2 zero_le_one⟩ hW_cont
  set A := W τ₀
  have hA_nn : 0 ≤ A := mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
  have hw_bound : ∀ r ∈ Icc (0 : ℝ) 1, ‖w r‖ ≤ A * Real.exp (D₁.lam * (r - 0)) := by
    intro r hr
    rw [hlam]
    have hle : Real.exp (-D₀.lam * r) * ‖w r‖ ≤ A := hτ₀_max hr
    calc ‖w r‖
        = Real.exp (D₀.lam * r) * (Real.exp (-D₀.lam * r) * ‖w r‖) := by
          rw [← mul_assoc, ← Real.exp_add]
          ring_nf
          rw [Real.exp_zero, one_mul]
      _ ≤ Real.exp (D₀.lam * r) * A := mul_le_mul_of_nonneg_left hle (Real.exp_pos _).le
      _ = A * Real.exp (D₀.lam * (r - 0)) := by rw [sub_zero, mul_comm]
  have hτ₀_strip : τ₀ ∈ Icc (0 : ℝ) (0 + 1) := ⟨hτ₀.1, by linarith [hτ₀.2]⟩
  have heq_1 := D₁.stripEvolution_eq hτ₀_strip x
  have heq_0 := D₀.stripEvolution_eq hτ₀_strip x
  have hi_1 : IntervalIntegrable (fun r => D₀.S (τ₀ - r) (D₁.B r (u₁ r))) volume 0 τ₀ := by
    rw [← hS]
    exact D₁.intervalIntegrable_integrand hτ₀.1 hτ₀_strip.2
      (hu₁_cont.mono (Icc_subset_Icc_right hτ₀.2))
  have hi_0 : IntervalIntegrable (fun r => D₀.S (τ₀ - r) (D₀.B r (u r))) volume 0 τ₀ :=
    D₀.intervalIntegrable_integrand hτ₀.1 hτ₀_strip.2 (hu_cont.mono (Icc_subset_Icc_right hτ₀.2))
  have hi_vol : IntervalIntegrable (fun r => D₁.S (τ₀ - r) (D₁.B r (w r))) volume 0 τ₀ :=
    D₁.intervalIntegrable_integrand hτ₀.1 hτ₀_strip.2
      ((hu₁_cont.sub hu_cont).mono (Icc_subset_Icc_right hτ₀.2))
  have hi_rem : IntervalIntegrable
      (fun r => D₀.S (τ₀ - r) (D₁.B r (u r) - D₀.B r (u r))) volume 0 τ₀ := by
    have hfn : (fun r => D₀.S (τ₀ - r) (D₁.B r (u r) - D₀.B r (u r))) =
        fun r => (D₀.S (τ₀ - r) (D₁.B r (u₁ r)) - D₀.S (τ₀ - r) (D₀.B r (u r))) -
          D₁.S (τ₀ - r) (D₁.B r (w r)) := by
      funext r
      dsimp only [w]
      rw [hS, map_sub, map_sub, map_sub]
      abel
    rw [hfn]
    exact (hi_1.sub hi_0).sub hi_vol
  have hw_eq : w τ₀ = D₁.vol 0 w τ₀ +
      ∫ r in (0 : ℝ)..τ₀, D₀.S (τ₀ - r) (D₁.B r (u r) - D₀.B r (u r)) := by
    dsimp only [w, u₁, u, VolterraData.vol]
    rw [heq_1, heq_0, hS₀, add_sub_add_left_eq_sub]
    simp only [hS]
    rw [← intervalIntegral.integral_sub hi_1 hi_0,
      ← intervalIntegral.integral_add (by simpa only [hS] using hi_vol) hi_rem]
    refine intervalIntegral.integral_congr fun r _ => ?_
    rw [map_sub, map_sub, map_sub]
    abel
  have hlam1_pos : 0 < D₁.lam := hlam ▸ D₀.lam_pos
  have hvol_le : ‖D₁.vol 0 w τ₀‖ ≤ (1 / 2 : ℝ) * A * Real.exp (D₀.lam * τ₀) := by
    have hv1 := D₁.norm_vol_le hlam1_pos hτ₀.1 hτ₀_strip.2
      (fun r hr => hw_bound r ⟨hr.1, hr.2.trans hτ₀.2⟩)
    have hq_eq : D₁.C₀ * D₁.β * A * ((1 / D₁.lam) ^ (1 / 2 : ℝ) * Real.Gamma (1 / 2) *
        Real.exp (D₁.lam * (τ₀ - 0))) = D₀.q * A * Real.exp (D₀.lam * τ₀) := by
      rw [hC₀, hβ, hlam, sub_zero]
      unfold VolterraData.q
      ring
    rw [hq_eq] at hv1
    exact hv1.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right D₀.q_le_half hA_nn) (Real.exp_pos _).le)
  have hrem_le : ‖∫ r in (0 : ℝ)..τ₀, D₀.S (τ₀ - r) (D₁.B r (u r) - D₀.B r (u r))‖ ≤
      2 * D₀.C₀ * η := by
    have hker : IntervalIntegrable
        (fun r : ℝ => D₀.C₀ * η * (τ₀ - r) ^ (-(1 / 2 : ℝ))) volume 0 τ₀ :=
      (intervalIntegrable_kernel τ₀ 0 τ₀).const_mul (D₀.C₀ * η)
    have hae : ∀ᵐ r ∂volume, r ∈ Ioc 0 τ₀ →
        ‖D₀.S (τ₀ - r) (D₁.B r (u r) - D₀.B r (u r))‖ ≤
          D₀.C₀ * η * (τ₀ - r) ^ (-(1 / 2 : ℝ)) := by
      filter_upwards [ae_ne_real τ₀] with r hr_ne hr
      have hpos : 0 < τ₀ - r := sub_pos.mpr (lt_of_le_of_ne hr.2 hr_ne)
      have hle1 : τ₀ - r ≤ 1 := by linarith [hr.1, hτ₀.2]
      have hS_le := D₀.norm_S_le (τ₀ - r) hpos hle1
      have hB := hB_err r ⟨hr.1.le, hr.2.trans hτ₀.2⟩
      calc ‖D₀.S (τ₀ - r) (D₁.B r (u r) - D₀.B r (u r))‖
          ≤ ‖D₀.S (τ₀ - r)‖ * ‖D₁.B r (u r) - D₀.B r (u r)‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ (D₀.C₀ * (τ₀ - r) ^ (-(1 / 2 : ℝ))) * η :=
            mul_le_mul hS_le hB (norm_nonneg _) ((norm_nonneg _).trans hS_le)
        _ = D₀.C₀ * η * (τ₀ - r) ^ (-(1 / 2 : ℝ)) := by ring
    have hint_le := intervalIntegral.norm_integral_le_of_norm_le hτ₀.1 hae hker
    have hval : ∫ r in (0 : ℝ)..τ₀, D₀.C₀ * η * (τ₀ - r) ^ (-(1 / 2 : ℝ)) =
        D₀.C₀ * η * (2 * (τ₀ - 0) ^ (1 / 2 : ℝ)) := by
      rw [intervalIntegral.integral_const_mul, integral_kernel]
    have hrpow_le : (τ₀ - 0) ^ (1 / 2 : ℝ) ≤ 1 := by
      rw [sub_zero]
      exact Real.rpow_le_one hτ₀.1 hτ₀.2 (by norm_num)
    calc ‖∫ r in (0 : ℝ)..τ₀, D₀.S (τ₀ - r) (D₁.B r (u r) - D₀.B r (u r))‖
        ≤ D₀.C₀ * η * (2 * (τ₀ - 0) ^ (1 / 2 : ℝ)) := hint_le.trans_eq hval
      _ ≤ D₀.C₀ * η * (2 * 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrpow_le zero_le_two)
            (mul_nonneg hC₀_nn hη)
      _ = 2 * D₀.C₀ * η := by ring
  have hw_τ₀ : ‖w τ₀‖ ≤ (1 / 2 : ℝ) * A * Real.exp (D₀.lam * τ₀) + 2 * D₀.C₀ * η := by
    rw [hw_eq]
    exact (norm_add_le _ _).trans (add_le_add hvol_le hrem_le)
  have hA_le : A ≤ 4 * D₀.C₀ * η := by
    have hexp_le1 : Real.exp (-D₀.lam * τ₀) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [D₀.lam_pos, hτ₀.1])
    have hm := mul_le_mul_of_nonneg_left hw_τ₀ (Real.exp_pos (-D₀.lam * τ₀)).le
    have h1 : Real.exp (-D₀.lam * τ₀) * ((1 / 2 : ℝ) * A * Real.exp (D₀.lam * τ₀) +
        2 * D₀.C₀ * η) = (1 / 2 : ℝ) * A + Real.exp (-D₀.lam * τ₀) * (2 * D₀.C₀ * η) := by
      have hexp0 : Real.exp (-D₀.lam * τ₀) * Real.exp (D₀.lam * τ₀) = 1 := by
        rw [← Real.exp_add]
        ring_nf
        exact Real.exp_zero
      linear_combination (1 / 2 : ℝ) * A * hexp0
    have h2 : Real.exp (-D₀.lam * τ₀) * (2 * D₀.C₀ * η) ≤ 2 * D₀.C₀ * η :=
      mul_le_of_le_one_left (mul_nonneg (mul_nonneg zero_le_two hC₀_nn) hη) hexp_le1
    have h3 : A ≤ (1 / 2 : ℝ) * A + 2 * D₀.C₀ * η := by
      dsimp only [A, W]
      linarith [hm, h1, h2]
    linarith
  have hwt := hw_bound τ hτ
  rw [hlam] at hwt
  have hexp_le : Real.exp (D₀.lam * (τ - 0)) ≤ Real.exp D₀.lam :=
    Real.exp_le_exp.mpr (by nlinarith [D₀.lam_pos, hτ.2])
  calc ‖w τ‖
      ≤ A * Real.exp (D₀.lam * (τ - 0)) := hwt
    _ ≤ (4 * D₀.C₀ * η) * Real.exp D₀.lam :=
        mul_le_mul hA_le hexp_le (Real.exp_pos _).le (by positivity)
    _ = (4 * D₀.C₀ * Real.exp D₀.lam) * η := by ring

private lemma bvRegCLM_sub_bvCLM {c : ℝ} (hc : 0 < c) {V : ℝ → Plane → F8Ex.RMerid}
    (hV : F8Ex.IsSmoothBUCDrift c V) (ε r : ℝ) (p : H1Sol c) :
    bvRegCLM hc hV ε r p - bvCLM hc hV r p =
      centeredHeatVecL2CLM hc ε (bvCLM hc hV r (freeH1CLM hc ε p - p)) +
        (centeredHeatVecL2CLM hc ε (bvCLM hc hV r p) - bvCLM hc hV r p) := by
  unfold bvRegCLM
  dsimp only [ContinuousLinearMap.comp_apply]
  rw [map_sub, map_sub]
  abel

/-- Pointwise-in-time `H1Sol c` convergence `E_oseenReg ε t 0 u₀ → E_oseen t 0 u₀` as `ε → 0`. -/
lemma tendsto_E_oseenReg {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν) {V : ℝ → Plane → F8Ex.RMerid}
    (hV : F8Ex.IsSmoothBUCDrift c V) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 2) (u₀ : H1Sol c) :
    Tendsto (fun ε : ℝ => E_oseenReg hc hν hV ε t 0 u₀)
      (𝓝 0) (𝓝 (E_oseen hc hν hV t 0 u₀)) := by
  have hu_cont : ContinuousOn
      (fun σ => (oseenVolterraData hc hν hV).stripEvolution σ 0 u₀) (Icc 0 1) := by
    simpa using (oseenVolterraData hc hν hV).continuousOn_stripEvolution 0 u₀
  have hv_cont : ContinuousOn
      (fun σ => (oseenVolterraData hc hν hV).B σ
        ((oseenVolterraData hc hν hV).stripEvolution σ 0 u₀)) (Icc 0 1) :=
    (oseenVolterraData hc hν hV).continuousOn_B_apply hu_cont
  rw [Metric.tendsto_nhds]
  intro δ hδ
  let C₀ := (oseenVolterraData hc hν hV).C₀
  let β := (oseenVolterraData hc hν hV).β
  let lam := (oseenVolterraData hc hν hV).lam
  have hC₀_nn : 0 ≤ C₀ := (oseenVolterraData hc hν hV).C₀_nonneg
  have hβ_nn : 0 ≤ β := (oseenVolterraData hc hν hV).β_nonneg
  let K : ℝ := 4 * (C₀ + 1) * Real.exp lam
  have hK_pos : 0 < K := by dsimp only [K]; positivity
  let η : ℝ := δ / (2 * K)
  have hη : 0 < η := div_pos hδ (by positivity)
  have hev1 : ∀ᶠ ε : ℝ in 𝓝 0, ∀ σ ∈ Icc (0 : ℝ) 1,
      ‖freeH1CLM hc ε ((oseenVolterraData hc hν hV).stripEvolution σ 0 u₀) -
          (oseenVolterraData hc hν hV).stripEvolution σ 0 u₀‖ < η / (2 * (β + 1)) :=
    eventually_uniform_contraction_on_Icc (norm_freeH1CLM_le hc)
      (fun p => by
        have hp := (continuous_freeH1CLM_apply hc p).tendsto 0
        rwa [freeH1CLM_of_nonpos hc le_rfl, ContinuousLinearMap.id_apply] at hp)
      hu_cont (div_pos hη (by positivity))
  have hev2 : ∀ᶠ ε : ℝ in 𝓝 0, ∀ σ ∈ Icc (0 : ℝ) 1,
      ‖centeredHeatVecL2CLM hc ε
          ((oseenVolterraData hc hν hV).B σ
            ((oseenVolterraData hc hν hV).stripEvolution σ 0 u₀)) -
          (oseenVolterraData hc hν hV).B σ
            ((oseenVolterraData hc hν hV).stripEvolution σ 0 u₀)‖ < η / 2 :=
    eventually_uniform_contraction_on_Icc (norm_centeredHeatVecL2CLM_le_one_all hc)
      (fun y => by
        have hy := (continuous_centeredHeatVecL2CLM_apply hc y).tendsto 0
        rwa [centeredHeatVecL2CLM_eq_id_of_nonpos hc le_rfl, ContinuousLinearMap.id_apply] at hy)
      hv_cont (half_pos hη)
  filter_upwards [hev1, hev2] with ε hε1 hε2
  have hB_err : ∀ σ ∈ Icc (0 : ℝ) 1,
      ‖(oseenRegVolterraData hc hν hV ε).B σ
          ((oseenVolterraData hc hν hV).stripEvolution σ 0 u₀) -
        (oseenVolterraData hc hν hV).B σ
          ((oseenVolterraData hc hν hV).stripEvolution σ 0 u₀)‖ ≤ η := by
    intro σ hσ
    let p := (oseenVolterraData hc hν hV).stripEvolution σ 0 u₀
    have hB1 : (oseenRegVolterraData hc hν hV ε).B σ p = bvRegCLM hc hV ε (2 * σ) p := rfl
    have hB0 : (oseenVolterraData hc hν hV).B σ p = bvCLM hc hV (2 * σ) p := rfl
    have hB0' : ∀ q, bvCLM hc hV (2 * σ) q = (oseenVolterraData hc hν hV).B σ q := fun _ => rfl
    rw [hB1, hB0, bvRegCLM_sub_bvCLM, hB0', hB0']
    have hb1 : ‖centeredHeatVecL2CLM hc ε
        ((oseenVolterraData hc hν hV).B σ (freeH1CLM hc ε p - p))‖ ≤
        β * ‖freeH1CLM hc ε p - p‖ := by
      calc ‖centeredHeatVecL2CLM hc ε
            ((oseenVolterraData hc hν hV).B σ (freeH1CLM hc ε p - p))‖
          ≤ 1 * ‖(oseenVolterraData hc hν hV).B σ (freeH1CLM hc ε p - p)‖ :=
            (ContinuousLinearMap.le_opNorm _ _).trans
              (mul_le_mul_of_nonneg_right
                (norm_centeredHeatVecL2CLM_le_one_all hc ε) (norm_nonneg _))
        _ ≤ β * ‖freeH1CLM hc ε p - p‖ := by
            rw [one_mul]
            exact (ContinuousLinearMap.le_opNorm _ _).trans
              (mul_le_mul_of_nonneg_right
                ((oseenVolterraData hc hν hV).norm_B_le σ) (norm_nonneg _))
    have hlt1 := hε1 σ hσ
    have hdiv1 : β * ‖freeH1CLM hc ε p - p‖ ≤ η / 2 := by
      have hpos : 0 < 2 * (β + 1) := by positivity
      have hm : ‖freeH1CLM hc ε p - p‖ * (2 * (β + 1)) ≤ η :=
        (le_div_iff₀ hpos).1 hlt1.le
      nlinarith [norm_nonneg (freeH1CLM hc ε p - p)]
    exact (norm_add_le _ _).trans (by linarith [hb1, hdiv1, (hε2 σ hσ).le])
  have hτ_mem : t / 2 ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hstab := norm_stripEvolution_sub_le_of_B_err
    (oseenVolterraData hc hν hV) (oseenRegVolterraData hc hν hV ε)
    rfl rfl rfl rfl rfl rfl u₀ hη.le hB_err hτ_mem
  have h0 : (0 : ℝ) / 2 = 0 := by norm_num
  have hdist_eq : dist (E_oseenReg hc hν hV ε t 0 u₀) (E_oseen hc hν hV t 0 u₀) =
      ‖(oseenRegVolterraData hc hν hV ε).stripEvolution (t / 2) 0 u₀ -
        (oseenVolterraData hc hν hV).stripEvolution (t / 2) 0 u₀‖ := by
    unfold E_oseenReg E_oseen
    rw [h0, dist_eq_norm]
  rw [hdist_eq]
  calc ‖(oseenRegVolterraData hc hν hV ε).stripEvolution (t / 2) 0 u₀ -
          (oseenVolterraData hc hν hV).stripEvolution (t / 2) 0 u₀‖
      ≤ (4 * C₀ * Real.exp lam) * η := hstab
    _ < (4 * (C₀ + 1) * Real.exp lam) * η := by
        have : 0 < 4 * Real.exp lam * η := by positivity
        linarith
    _ = δ / 2 := by
        dsimp only [K, η]
        field_simp [hK_pos.ne']
    _ < δ := half_lt_self hδ

/-! ## 3. Smooth Derivative Tower `uReg` and Exact `L2v c` ODE on `(0, 2)` -/

/-- Inner-regularized drift forcing `bvCLM r (freeH1CLM ε (E_oseenReg ε r 0 u₀))`. -/
def fReg {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν) {V : ℝ → Plane → F8Ex.RMerid}
    (hV : F8Ex.IsSmoothBUCDrift c V) (u₀ : H1Sol c) (ε r : ℝ) : L2v c :=
  bvCLM hc hV r (freeH1CLM hc ε (E_oseenReg hc hν hV ε r 0 u₀))

lemma continuousOn_fReg {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν) {V : ℝ → Plane → F8Ex.RMerid}
    (hV : F8Ex.IsSmoothBUCDrift c V) (u₀ : H1Sol c) (ε : ℝ) :
    ContinuousOn (fReg hc hν hV u₀ ε) (Icc (0 : ℝ) 2) :=
  continuousOn_clm_apply (fun p => (continuous_bvCLM_apply hc hV p).continuousOn)
    (fun _ _ => ⟨6 * driftBound hV, Eventually.of_forall fun r => norm_bvCLM_le hc hV r⟩)
    ((freeH1CLM hc ε).continuous.comp_continuousOn
      (continuousOn_E_oseenReg hc hν hV ε ⟨le_rfl, zero_le_two⟩ u₀))

lemma norm_fReg_le {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν) {V : ℝ → Plane → F8Ex.RMerid}
    (hV : F8Ex.IsSmoothBUCDrift c V) (u₀ : H1Sol c) (ε r : ℝ) :
    ‖fReg hc hν hV u₀ ε r‖ ≤
      (6 * driftBound hV) * ((oseenVolterraData hc hν hV).stripBound * ‖u₀‖) := by
  have hdb : 0 ≤ 6 * driftBound hV :=
    (norm_nonneg (bvCLM hc hV r)).trans (norm_bvCLM_le hc hV r)
  calc ‖bvCLM hc hV r (freeH1CLM hc ε (E_oseenReg hc hν hV ε r 0 u₀))‖
      ≤ (6 * driftBound hV) * ‖freeH1CLM hc ε (E_oseenReg hc hν hV ε r 0 u₀)‖ :=
        (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right (norm_bvCLM_le hc hV r) (norm_nonneg _))
    _ ≤ (6 * driftBound hV) * (1 * ‖E_oseenReg hc hν hV ε r 0 u₀‖) :=
        mul_le_mul_of_nonneg_left
          ((ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul_of_nonneg_right (norm_freeH1CLM_le hc ε) (norm_nonneg _)))
          hdb
    _ ≤ (6 * driftBound hV) * ((oseenVolterraData hc hν hV).stripBound * ‖u₀‖) := by
        rw [one_mul]
        exact mul_le_mul_of_nonneg_left (norm_E_oseenReg_le hc hν hV ε r 0 u₀) hdb

/-- Duhamel integrand `P₀ (iterDHeatCLM hc α (ν(t - r) + ε) (fReg ε r))` for `uReg`. -/
def duhRegIntegrand {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν) {V : ℝ → Plane → F8Ex.RMerid}
    (hV : F8Ex.IsSmoothBUCDrift c V) (u₀ : H1Sol c)
    (ε : ℝ) (α : List (Fin 2)) (t r : ℝ) : L2v c :=
  P0 c (iterDHeatCLM hc α (ν * (t - r) + ε) (fReg hc hν hV u₀ ε r))

/-- Smooth `L2v c` spatial derivative tower of `E_oseenReg ε t 0 u₀` for `ε > 0`, `t > 0`. -/
def uReg {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν) {V : ℝ → Plane → F8Ex.RMerid}
    (hV : F8Ex.IsSmoothBUCDrift c V) (u₀ : H1Sol c)
    (ε : ℝ) (α : List (Fin 2)) (t : ℝ) : L2v c :=
  iterDHeatCLM hc α (ν * t) (val0CLM c u₀) -
    ∫ r in (0 : ℝ)..t, duhRegIntegrand hc hν hV u₀ ε α t r

/-- Factorization of `duhRegIntegrand` whenever `ν(t - r) + ε > ε / 2`, making joint `(t, r)`
continuity immediate. -/
private lemma duhRegIntegrand_eq_factored {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν)
    {V : ℝ → Plane → F8Ex.RMerid} (hV : F8Ex.IsSmoothBUCDrift c V) (u₀ : H1Sol c)
    {ε : ℝ} (hε : 0 < ε) (α : List (Fin 2)) {t r : ℝ}
    (hpos : ε / 2 < ν * (t - r) + ε) :
    duhRegIntegrand hc hν hV u₀ ε α t r =
      P0 c (centeredHeatVecL2CLM hc (ν * (t - r) + ε / 2)
        (iterDHeatCLM hc α (ε / 2) (fReg hc hν hV u₀ ε r))) := by
  unfold duhRegIntegrand
  congr 1
  have h1 : 0 < ν * (t - r) + ε / 2 := by linarith
  have h2 : 0 < ε / 2 := half_pos hε
  have hsum : (ν * (t - r) + ε / 2) + ε / 2 = ν * (t - r) + ε := by ring
  rw [← hsum]
  exact iterDHeatCLM_add_left hc α h1 h2 _

private lemma continuousOn_duhRegIntegrand_slice {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν)
    {V : ℝ → Plane → F8Ex.RMerid} (hV : F8Ex.IsSmoothBUCDrift c V) (u₀ : H1Sol c)
    {ε : ℝ} (hε : 0 < ε) (α : List (Fin 2)) (t : ℝ)
    {a b : ℝ} (hab_lo : 0 ≤ min a b) (hab_hi : max a b ≤ 2)
    (hage : ∀ r ∈ uIcc a b, ε / 2 < ν * (t - r) + ε) :
    ContinuousOn (duhRegIntegrand hc hν hV u₀ ε α t) (uIcc a b) := by
  have hsub : uIcc a b ⊆ Icc (0 : ℝ) 2 := by
    intro r hr
    rw [uIcc] at hr
    exact ⟨hab_lo.trans hr.1, hr.2.trans hab_hi⟩
  let g : ℝ → L2v c := fun r => iterDHeatCLM hc α (ε / 2) (fReg hc hν hV u₀ ε r)
  have hg : ContinuousOn g (uIcc a b) :=
    (iterDHeatCLM hc α (ε / 2)).continuous.comp_continuousOn
      ((continuousOn_fReg hc hν hV u₀ ε).mono hsub)
  have hH : ContinuousOn
      (fun r => P0 c (centeredHeatVecL2CLM hc (ν * (t - r) + ε / 2) (g r))) (uIcc a b) := by
    refine (P0 c).continuous.comp_continuousOn ?_
    refine continuousOn_clm_apply
      (fun y => ((continuous_centeredHeatVecL2CLM_apply hc y).comp
        ((continuous_const.mul (continuous_const.sub continuous_id)).add
          continuous_const)).continuousOn)
      (fun _ _ => ⟨1, Eventually.of_forall fun r =>
        norm_centeredHeatVecL2CLM_le_one_all hc (ν * (t - r) + ε / 2)⟩) hg
  exact hH.congr fun r hr => duhRegIntegrand_eq_factored hc hν hV u₀ hε α (hage r hr)

lemma intervalIntegrable_duhRegIntegrand {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν)
    {V : ℝ → Plane → F8Ex.RMerid} (hV : F8Ex.IsSmoothBUCDrift c V) (u₀ : H1Sol c)
    {ε : ℝ} (hε : 0 < ε) (α : List (Fin 2)) (t : ℝ)
    {a b : ℝ} (hab_lo : 0 ≤ min a b) (hab_hi : max a b ≤ 2)
    (hage : ∀ r ∈ uIcc a b, ε / 2 < ν * (t - r) + ε) :
    IntervalIntegrable (duhRegIntegrand hc hν hV u₀ ε α t) volume a b :=
  (continuousOn_duhRegIntegrand_slice hc hν hV u₀ hε α t hab_lo hab_hi hage).intervalIntegrable

lemma uReg_nil_eq {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν)
    {V : ℝ → Plane → F8Ex.RMerid} (hV : F8Ex.IsSmoothBUCDrift c V) (u₀ : H1Sol c)
    {ε : ℝ} (hε : 0 < ε) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 2) :
    uReg hc hν hV u₀ ε [] t = val0CLM c (E_oseenReg hc hν hV ε t 0 u₀) := by
  obtain ⟨hint, hmild⟩ := E_oseenReg_mild hc hν hV ε ht.1 ht.2 u₀
  have hval := congrArg (val0CLM c) hmild
  rw [map_sub, val0_freeH1CLM, ← (val0CLM c).intervalIntegral_comp_comm hint] at hval
  rw [hval]
  unfold uReg
  have hfree_eq : iterDHeatCLM hc [] (ν * t) (val0CLM c u₀) =
      centeredHeatVecL2CLM hc (ν * t) (val0CLM c u₀) := rfl
  rw [hfree_eq]
  refine congrArg (centeredHeatVecL2CLM hc (ν * t) (val0CLM c u₀) - ·) ?_
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [ae_ne_real t] with r hr_ne hr
  rw [uIoc_of_le ht.1] at hr
  have hpos : 0 < ν * (t - r) := mul_pos hν (sub_pos.mpr (lt_of_le_of_ne hr.2 hr_ne))
  rw [val0_duhH1CLM_of_pos hc hpos]
  unfold duhRegIntegrand iterDHeatCLM bvRegCLM fReg
  dsimp only [ContinuousLinearMap.comp_apply]
  congr 1
  exact (congrArg (fun L : L2v c →L[ℝ] L2v c =>
    L (bvCLM hc hV r (freeH1CLM hc ε (E_oseenReg hc hν hV ε r 0 u₀))))
    (centeredHeatVecL2CLM_comp_of_nonneg hc hpos.le hε.le)).symm

lemma uReg_mem_divFree {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν)
    {V : ℝ → Plane → F8Ex.RMerid} (hV : F8Ex.IsSmoothBUCDrift c V) (u₀ : H1Sol c)
    {ε : ℝ} (hε : 0 < ε) (α : List (Fin 2)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 2) :
    uReg hc hν hV u₀ ε α t ∈ divFree c := by
  unfold uReg
  have hfree : iterDHeatCLM hc α (ν * t) (val0CLM c u₀) ∈ divFree c := by
    have hp0 : P0 c (val0CLM c u₀) = val0CLM c u₀ :=
      Cyl.P0_eq_self (H1Sol.mem_divFree u₀)
    rw [← hp0, iterDHeatCLM_P0_comm hc]
    exact Cyl.P0_mem _
  have hint_raw : IntervalIntegrable
      (fun r => iterDHeatCLM hc α (ν * (t - r) + ε) (fReg hc hν hV u₀ ε r)) volume 0 t := by
    have hage : ∀ r ∈ uIcc (0 : ℝ) t, ε / 2 < ν * (t - r) + ε := by
      rw [uIcc_of_le ht.1]
      intro r hr
      have : 0 ≤ ν * (t - r) := mul_nonneg hν.le (sub_nonneg.mpr hr.2)
      linarith
    let g : ℝ → L2v c := fun r => iterDHeatCLM hc α (ε / 2) (fReg hc hν hV u₀ ε r)
    have hg : ContinuousOn g (uIcc 0 t) := by
      rw [uIcc_of_le ht.1]
      exact (iterDHeatCLM hc α (ε / 2)).continuous.comp_continuousOn
        ((continuousOn_fReg hc hν hV u₀ ε).mono (Icc_subset_Icc_right ht.2))
    have hc_on : ContinuousOn
        (fun r => centeredHeatVecL2CLM hc (ν * (t - r) + ε / 2) (g r)) (uIcc 0 t) :=
      continuousOn_clm_apply
        (fun y => ((continuous_centeredHeatVecL2CLM_apply hc y).comp
          ((continuous_const.mul (continuous_const.sub continuous_id)).add
            continuous_const)).continuousOn)
        (fun _ _ => ⟨1, Eventually.of_forall fun r =>
          norm_centeredHeatVecL2CLM_le_one_all hc (ν * (t - r) + ε / 2)⟩) hg
    refine (hc_on.congr fun r hr => ?_).intervalIntegrable
    have h1 : 0 < ν * (t - r) + ε / 2 := by linarith [hage r hr]
    have h2 : 0 < ε / 2 := half_pos hε
    have hsum : (ν * (t - r) + ε / 2) + ε / 2 = ν * (t - r) + ε := by ring
    rw [← hsum]
    exact iterDHeatCLM_add_left hc α h1 h2 _
  have hduh : (∫ r in (0 : ℝ)..t, duhRegIntegrand hc hν hV u₀ ε α t r) ∈ divFree c := by
    unfold duhRegIntegrand
    have hcomm := (P0 c).intervalIntegral_comp_comm hint_raw
    rw [hcomm]
    exact Cyl.P0_mem _
  exact (divFree c).sub_mem hfree hduh

lemma hasWeakDeriv1_uReg {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν)
    {V : ℝ → Plane → F8Ex.RMerid} (hV : F8Ex.IsSmoothBUCDrift c V) (u₀ : H1Sol c)
    {ε : ℝ} (hε : 0 < ε) (j : Fin 2) (α : List (Fin 2)) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 2) :
    HasWeakDeriv1 c j (uReg hc hν hV u₀ ε α t) (uReg hc hν hV u₀ ε (j :: α) t) := by
  have hfree := hasWeakDeriv1_iterDHeatCLM hc j α (mul_pos hν ht.1) (val0CLM c u₀)
  have hlo : 0 ≤ min (0 : ℝ) t := by simp [ht.1.le]
  have hhi : max (0 : ℝ) t ≤ 2 := max_le zero_le_two ht.2
  have hage : ∀ r ∈ uIcc (0 : ℝ) t, ε / 2 < ν * (t - r) + ε := by
    rw [uIcc_of_le ht.1.le]
    intro r hr
    have : 0 ≤ ν * (t - r) := mul_nonneg hν.le (sub_nonneg.mpr hr.2)
    linarith
  have hi0 := intervalIntegrable_duhRegIntegrand hc hν hV u₀ hε α t hlo hhi hage
  have hi1 := intervalIntegrable_duhRegIntegrand hc hν hV u₀ hε (j :: α) t hlo hhi hage
  have hpt : ∀ r ∈ Icc (0 : ℝ) t,
      HasWeakDeriv1 c j (duhRegIntegrand hc hν hV u₀ ε α t r)
        (duhRegIntegrand hc hν hV u₀ ε (j :: α) t r) := by
    intro r hr
    have hpos : 0 < ν * (t - r) + ε := by
      have : 0 ≤ ν * (t - r) := mul_nonneg hν.le (sub_nonneg.mpr hr.2)
      linarith
    have hw0 := hasWeakDeriv1_iterDHeatCLM hc 0 α hpos (fReg hc hν hV u₀ ε r)
    have hw1 := hasWeakDeriv1_iterDHeatCLM hc 1 α hpos (fReg hc hν hV u₀ ε r)
    have hp0 := hasWeakCellDerivR_P0 hc hw0 hw1
    fin_cases j
    · exact hp0.1
    · exact hp0.2
  exact hfree.sub (HasWeakDeriv1.intervalIntegral ht.1.le hi0 hi1 hpt)

lemma hasIterWeakDeriv_uReg {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν)
    {V : ℝ → Plane → F8Ex.RMerid} (hV : F8Ex.IsSmoothBUCDrift c V) (u₀ : H1Sol c)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ (α : List (Fin 2)) {t : ℝ}, t ∈ Ioc (0 : ℝ) 2 →
      HasIterWeakDeriv c α (val0CLM c (E_oseenReg hc hν hV ε t 0 u₀))
        (uReg hc hν hV u₀ ε α t)
  | [], _, ht => (uReg_nil_eq hc hν hV u₀ hε ⟨ht.1.le, ht.2⟩).symm
  | j :: α, t, ht =>
      ⟨uReg hc hν hV u₀ ε α t, hasIterWeakDeriv_uReg hc hν hV u₀ hε α ht,
        hasWeakDeriv1_uReg hc hν hV u₀ hε j α ht⟩

/-- Pointwise `t`-derivative and uniform norm bound of `duhRegIntegrand` whenever
`ν(t - r) + ε ≥ 3ε / 4`. -/
private lemma hasDerivAt_duhRegIntegrand {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν)
    {V : ℝ → Plane → F8Ex.RMerid} (hV : F8Ex.IsSmoothBUCDrift c V) (u₀ : H1Sol c)
    {ε : ℝ} (_hε : 0 < ε) (α : List (Fin 2)) {t r : ℝ}
    (hpos : 0 < ν * (t - r) + ε) :
    HasDerivAt (fun s => duhRegIntegrand hc hν hV u₀ ε α s r)
      (ν • (duhRegIntegrand hc hν hV u₀ ε (0 :: 0 :: α) t r +
        duhRegIntegrand hc hν hV u₀ ε (1 :: 1 :: α) t r)) t := by
  have hd_age : HasDerivAt (fun s : ℝ => ν * (s - r) + ε) ν t := by
    have h1 : HasDerivAt (fun s : ℝ => s - r) 1 t := by
      simpa using (hasDerivAt_id t).sub_const r
    have h2 : HasDerivAt (fun s : ℝ => ν * (s - r)) (ν * 1) t := h1.const_mul ν
    simpa using h2.add_const ε
  have hd_it := (hasDerivAt_iterDHeatCLM hc α hpos (fReg hc hν hV u₀ ε r)).scomp t hd_age
  have hd_p0 := (P0 c).hasFDerivAt.comp_hasDerivAt t hd_it
  refine hd_p0.congr_deriv ?_
  rw [map_smul, map_add]
  rfl

/-- **Exact `L2v c` ODE on `(0, 2)` for the regularized derivative tower `uReg`**:
for every `ε > 0`, `α : List (Fin 2)`, and `t₀ ∈ (0, 2)`,
`(d/dt) uReg ε α t₀ = ν • (uReg ε (0::0::α) t₀ + uReg ε (1::1::α) t₀)
  - P₀ (iterDHeatCLM α ε (fReg ε t₀))`. -/
theorem hasDerivAt_uReg {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν)
    {V : ℝ → Plane → F8Ex.RMerid} (hV : F8Ex.IsSmoothBUCDrift c V) (u₀ : H1Sol c)
    {ε : ℝ} (hε : 0 < ε) (α : List (Fin 2)) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 2) :
    HasDerivAt (uReg hc hν hV u₀ ε α)
      (ν • (uReg hc hν hV u₀ ε (0 :: 0 :: α) t₀ + uReg hc hν hV u₀ ε (1 :: 1 :: α) t₀) -
        P0 c (iterDHeatCLM hc α ε (fReg hc hν hV u₀ ε t₀))) t₀ := by
  -- Free heat term derivative at `t₀ > 0`
  have hd_free : HasDerivAt (fun t => iterDHeatCLM hc α (ν * t) (val0CLM c u₀))
      (ν • (iterDHeatCLM hc (0 :: 0 :: α) (ν * t₀) (val0CLM c u₀) +
        iterDHeatCLM hc (1 :: 1 :: α) (ν * t₀) (val0CLM c u₀))) t₀ := by
    have hd_lin : HasDerivAt (fun t : ℝ => ν * t) ν t₀ := by
      simpa using (hasDerivAt_id t₀).const_mul ν
    exact (hasDerivAt_iterDHeatCLM hc α (mul_pos hν ht₀.1) (val0CLM c u₀)).scomp t₀ hd_lin
  -- Choose `δ > 0` so `(t₀ - δ, t₀ + δ) ⊆ (0, 2)` and `ν * 2δ ≤ ε / 4`
  set δ : ℝ := min (t₀ / 2) (min ((2 - t₀) / 2) (ε / (8 * ν)))
  have hδ_pos : 0 < δ :=
    lt_min (half_pos ht₀.1)
      (lt_min (half_pos (sub_pos.mpr ht₀.2)) (div_pos hε (by positivity)))
  have hδ_t0 : δ ≤ t₀ / 2 := min_le_left _ _
  have hδ_2t0 : δ ≤ (2 - t₀) / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδ_eps : δ ≤ ε / (8 * ν) := (min_le_right _ _).trans (min_le_right _ _)
  have hνδ : ν * δ ≤ ε / 8 := by
    have h8 : 0 < 8 * ν := by positivity
    have := (le_div_iff₀ h8).1 hδ_eps
    linarith
  let G := duhRegIntegrand hc hν hV u₀ ε α
  let G' : ℝ → ℝ → L2v c := fun s r =>
    ν • (duhRegIntegrand hc hν hV u₀ ε (0 :: 0 :: α) s r +
      duhRegIntegrand hc hν hV u₀ ε (1 :: 1 :: α) s r)
  set Mf : ℝ := (6 * driftBound hV) * ((oseenVolterraData hc hν hV).stripBound * ‖u₀‖)
  set K : ℝ := ν * (iterDHeatBound (0 :: 0 :: α) (ε / 2) +
      iterDHeatBound (1 :: 1 :: α) (ε / 2)) * Mf
  have hMf_nn : 0 ≤ Mf := (norm_nonneg _).trans (norm_fReg_le hc hν hV u₀ ε 0)
  have hK_nn : 0 ≤ K := by
    have b0 := iterDHeatBound_nonneg (0 :: 0 :: α) (half_pos hε)
    have b1 := iterDHeatBound_nonneg (1 :: 1 :: α) (half_pos hε)
    dsimp [K]
    positivity
  have hG'_bound : ∀ {s r : ℝ}, ε / 2 ≤ ν * (s - r) + ε → ‖G' s r‖ ≤ K := by
    intro s r hge
    have hP0 : ∀ z : L2v c, ‖P0 c z‖ ≤ ‖z‖ := fun z =>
      (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_of_le_one_left (norm_nonneg _) Cyl.norm_P0_le)
    have hb0 : ‖duhRegIntegrand hc hν hV u₀ ε (0 :: 0 :: α) s r‖ ≤
        iterDHeatBound (0 :: 0 :: α) (ε / 2) * Mf := by
      calc ‖P0 c (iterDHeatCLM hc (0 :: 0 :: α) (ν * (s - r) + ε) (fReg hc hν hV u₀ ε r))‖
          ≤ ‖iterDHeatCLM hc (0 :: 0 :: α) (ν * (s - r) + ε) (fReg hc hν hV u₀ ε r)‖ := hP0 _
        _ ≤ iterDHeatBound (0 :: 0 :: α) (ε / 2) * ‖fReg hc hν hV u₀ ε r‖ :=
            (ContinuousLinearMap.le_opNorm _ _).trans
              (mul_le_mul_of_nonneg_right
                (norm_iterDHeatCLM_le_of_ge hc (0 :: 0 :: α) (half_pos hε) hge) (norm_nonneg _))
        _ ≤ iterDHeatBound (0 :: 0 :: α) (ε / 2) * Mf :=
            mul_le_mul_of_nonneg_left (norm_fReg_le hc hν hV u₀ ε r)
              (iterDHeatBound_nonneg (0 :: 0 :: α) (half_pos hε))
    have hb1 : ‖duhRegIntegrand hc hν hV u₀ ε (1 :: 1 :: α) s r‖ ≤
        iterDHeatBound (1 :: 1 :: α) (ε / 2) * Mf := by
      calc ‖P0 c (iterDHeatCLM hc (1 :: 1 :: α) (ν * (s - r) + ε) (fReg hc hν hV u₀ ε r))‖
          ≤ ‖iterDHeatCLM hc (1 :: 1 :: α) (ν * (s - r) + ε) (fReg hc hν hV u₀ ε r)‖ := hP0 _
        _ ≤ iterDHeatBound (1 :: 1 :: α) (ε / 2) * ‖fReg hc hν hV u₀ ε r‖ :=
            (ContinuousLinearMap.le_opNorm _ _).trans
              (mul_le_mul_of_nonneg_right
                (norm_iterDHeatCLM_le_of_ge hc (1 :: 1 :: α) (half_pos hε) hge) (norm_nonneg _))
        _ ≤ iterDHeatBound (1 :: 1 :: α) (ε / 2) * Mf :=
            mul_le_mul_of_nonneg_left (norm_fReg_le hc hν hV u₀ ε r)
              (iterDHeatBound_nonneg (1 :: 1 :: α) (half_pos hε))
    dsimp [G', K]
    rw [norm_smul, Real.norm_of_nonneg hν.le]
    calc ν * ‖duhRegIntegrand hc hν hV u₀ ε (0 :: 0 :: α) s r +
            duhRegIntegrand hc hν hV u₀ ε (1 :: 1 :: α) s r‖
        ≤ ν * (iterDHeatBound (0 :: 0 :: α) (ε / 2) * Mf +
            iterDHeatBound (1 :: 1 :: α) (ε / 2) * Mf) :=
          mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add hb0 hb1)) hν.le
      _ = ν * (iterDHeatBound (0 :: 0 :: α) (ε / 2) +
            iterDHeatBound (1 :: 1 :: α) (ε / 2)) * Mf := by ring
  -- Age lower bound on `t ∈ (t₀ - δ, t₀ + δ)` and `r ≤ t₀ + δ`
  have hage_ball : ∀ {s r : ℝ}, s ∈ Ioo (t₀ - δ) (t₀ + δ) → r ≤ t₀ + δ →
      3 * ε / 4 < ν * (s - r) + ε := by
    intro s r hs hr
    have hsr : -2 * δ < s - r := by linarith [hs.1]
    have hmul : ν * (-2 * δ) < ν * (s - r) := mul_lt_mul_of_pos_left hsr hν
    linarith [hνδ]
  -- Part A: Differentiate `t ↦ ∫ r in 0..t₀, G t r` on `μ₀ = volume.restrict (Ioc 0 t₀)`
  let μ₀ : Measure ℝ := volume.restrict (Ioc 0 t₀)
  have : IsFiniteMeasure μ₀ :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioc]; exact ENNReal.ofReal_lt_top⟩
  have hball_nhds : Ioo (t₀ - δ) (t₀ + δ) ∈ 𝓝 t₀ :=
    Ioo_mem_nhds (by linarith) (by linarith)
  have hG_meas : ∀ᶠ s : ℝ in 𝓝 t₀, AEStronglyMeasurable (G s) μ₀ := by
    filter_upwards [hball_nhds] with s hs
    have hc_on := continuousOn_duhRegIntegrand_slice hc hν hV u₀ hε α s
      (a := 0) (b := t₀) (by simp [ht₀.1.le]) (max_le zero_le_two ht₀.2.le)
      (fun r hr => by
        rw [uIcc_of_le ht₀.1.le] at hr
        have := hage_ball hs (by linarith [hr.2] : r ≤ t₀ + δ)
        linarith)
    rw [uIcc_of_le ht₀.1.le] at hc_on
    exact (hc_on.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hG_int0 : Integrable (G t₀) μ₀ := by
    have hi := intervalIntegrable_duhRegIntegrand hc hν hV u₀ hε α t₀
      (a := 0) (b := t₀) (by simp [ht₀.1.le]) (max_le zero_le_two ht₀.2.le)
      (fun r hr => by
        rw [uIcc_of_le ht₀.1.le] at hr
        have : 0 ≤ ν * (t₀ - r) := mul_nonneg hν.le (sub_nonneg.mpr hr.2)
        linarith)
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le ht₀.1.le).1 hi
  have hG'_cont0 : ContinuousOn (G' t₀) (Icc 0 t₀) := by
    have hage0 : ∀ r ∈ uIcc (0 : ℝ) t₀, ε / 2 < ν * (t₀ - r) + ε := by
      rw [uIcc_of_le ht₀.1.le]
      intro r hr
      have : 0 ≤ ν * (t₀ - r) := mul_nonneg hν.le (sub_nonneg.mpr hr.2)
      linarith
    have c0 := continuousOn_duhRegIntegrand_slice hc hν hV u₀ hε (0 :: 0 :: α) t₀
      (a := 0) (b := t₀) (by simp [ht₀.1.le]) (max_le zero_le_two ht₀.2.le) hage0
    have c1 := continuousOn_duhRegIntegrand_slice hc hν hV u₀ hε (1 :: 1 :: α) t₀
      (a := 0) (b := t₀) (by simp [ht₀.1.le]) (max_le zero_le_two ht₀.2.le) hage0
    rw [uIcc_of_le ht₀.1.le] at c0 c1
    exact (c0.add c1).const_smul ν
  have hG'_meas0 : AEStronglyMeasurable (G' t₀) μ₀ :=
    (hG'_cont0.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hG'_dom : ∀ᵐ r ∂μ₀, ∀ s ∈ Ioo (t₀ - δ) (t₀ + δ), ‖G' s r‖ ≤ K := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr s hs
    have h34 := hage_ball hs (by linarith [hr.2] : r ≤ t₀ + δ)
    exact hG'_bound (by linarith)
  have hG_diff : ∀ᵐ r ∂μ₀, ∀ s ∈ Ioo (t₀ - δ) (t₀ + δ),
      HasDerivAt (fun u => G u r) (G' s r) s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr s hs
    have h34 := hage_ball hs (by linarith [hr.2] : r ≤ t₀ + δ)
    exact hasDerivAt_duhRegIntegrand hc hν hV u₀ hε α (by linarith)
  have hd_partA_raw := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ₀) (F := G) (F' := G') (bound := fun _ => K)
    hball_nhds hG_meas hG_int0 hG'_meas0 hG'_dom (integrable_const K) hG_diff).2
  have hd_partA : HasDerivAt (fun t => ∫ r in (0 : ℝ)..t₀, G t r)
      (∫ r in (0 : ℝ)..t₀, G' t₀ r) t₀ := by
    simp only [intervalIntegral.integral_of_le ht₀.1.le]
    exact hd_partA_raw
  -- Part B1: Differentiate `t ↦ ∫ r in t₀..t, G t₀ r` at `t₀` by continuity at `t₀`
  have hGt0_cont_near : ContinuousOn (G t₀) (uIcc (t₀ - δ / 2) (t₀ + δ / 2)) := by
    have ha_lo : 0 ≤ min (t₀ - δ / 2) (t₀ + δ / 2) := by
      rw [min_eq_left (by linarith)]
      linarith [hδ_t0]
    have hb_hi : max (t₀ - δ / 2) (t₀ + δ / 2) ≤ 2 := by
      rw [max_eq_right (by linarith)]
      linarith [hδ_2t0]
    refine continuousOn_duhRegIntegrand_slice hc hν hV u₀ hε α t₀ ha_lo hb_hi fun r hr => ?_
    rw [uIcc_of_le (by linarith)] at hr
    have h34 := hage_ball (s := t₀) ⟨by linarith, by linarith⟩
      (by linarith [hr.2] : r ≤ t₀ + δ)
    linarith
  have hGt0_contAt : ContinuousAt (G t₀) t₀ := by
    have hmem : Ioo (t₀ - δ / 2) (t₀ + δ / 2) ∈ 𝓝 t₀ :=
      Ioo_mem_nhds (by linarith) (by linarith)
    have hsub : Ioo (t₀ - δ / 2) (t₀ + δ / 2) ⊆ uIcc (t₀ - δ / 2) (t₀ + δ / 2) := by
      rw [uIcc_of_le (by linarith)]
      exact Ioo_subset_Icc_self
    exact (hGt0_cont_near.mono hsub).continuousAt hmem
  have hd_partB1 : HasDerivAt (fun t => ∫ r in t₀..t, G t₀ r)
      (P0 c (iterDHeatCLM hc α ε (fReg hc hν hV u₀ ε t₀))) t₀ := by
    have hGt0_self : G t₀ t₀ = P0 c (iterDHeatCLM hc α ε (fReg hc hν hV u₀ ε t₀)) := by
      dsimp [G, duhRegIntegrand]
      rw [sub_self, mul_zero, zero_add]
    rw [← hGt0_self, hasDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
    intro η hη
    have hcont_ev : ∀ᶠ r in 𝓝 t₀, ‖G t₀ r - G t₀ t₀‖ < η / 2 :=
      (tendsto_iff_norm_sub_tendsto_zero.mp hGt0_contAt.tendsto).eventually
        (gt_mem_nhds (half_pos hη))
    obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := Metric.eventually_nhds_iff_ball.mp hcont_ev
    have hm_pos : 0 < min (δ / 2) δ₁ := lt_min (half_pos hδ_pos) hδ₁_pos
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hm_pos] with h hh
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hh
    have hh_δ : |h| < δ / 2 := lt_of_lt_of_le hh (min_le_left _ _)
    have hh_1 : |h| < δ₁ := lt_of_lt_of_le hh (min_le_right _ _)
    have hint_h : IntervalIntegrable (G t₀) volume t₀ (t₀ + h) := by
      have hsub : uIcc t₀ (t₀ + h) ⊆ uIcc (t₀ - δ / 2) (t₀ + δ / 2) := by
        rw [uIcc_of_le (by linarith : t₀ - δ / 2 ≤ t₀ + δ / 2)]
        exact uIcc_subset_Icc ⟨by linarith, by linarith⟩
          ⟨by linarith [(abs_lt.mp hh_δ).1], by linarith [(abs_lt.mp hh_δ).2]⟩
      exact (hGt0_cont_near.mono hsub).intervalIntegrable
    have hconst_int : ∫ _r in t₀..(t₀ + h), G t₀ t₀ = h • G t₀ t₀ := by
      rw [intervalIntegral.integral_const, add_sub_cancel_left]
    rw [intervalIntegral.integral_same, sub_zero, ← hconst_int,
      ← intervalIntegral.integral_sub hint_h intervalIntegrable_const]
    have hbd : ∀ r ∈ uIoc t₀ (t₀ + h), ‖G t₀ r - G t₀ t₀‖ ≤ η := by
      intro r hr
      have hr_u : r ∈ uIcc t₀ (t₀ + h) := uIoc_subset_uIcc hr
      have hr_in : dist r t₀ < δ₁ := by
        rw [Real.dist_eq]
        have hr1 : t₀ - |h| ≤ r :=
          (le_min (by linarith [abs_nonneg h]) (by linarith [neg_abs_le h])).trans hr_u.1
        have hr2 : r ≤ t₀ + |h| :=
          hr_u.2.trans (max_le (by linarith [abs_nonneg h]) (by linarith [le_abs_self h]))
        exact lt_of_le_of_lt (abs_le.mpr ⟨by linarith, by linarith⟩) hh_1
      exact (hδ₁ r hr_in).le.trans (half_le_self hη.le)
    calc ‖∫ r in t₀..(t₀ + h), (G t₀ r - G t₀ t₀)‖
        ≤ η * |t₀ + h - t₀| := intervalIntegral.norm_integral_le_of_norm_le_const hbd
      _ = η * ‖h‖ := by rw [add_sub_cancel_left, Real.norm_eq_abs]
  -- Part B2: `t ↦ ∫ r in t₀..t, (G t r - G t₀ r)` is `O(|t - t₀|^2)` so has derivative `0`
  have hd_partB2 : HasDerivAt (fun t => ∫ r in t₀..t, (G t r - G t₀ r)) 0 t₀ := by
    rw [hasDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
    intro η hη
    have hδ2 : 0 < min (δ / 2) (η / (K + 1)) :=
      lt_min (half_pos hδ_pos) (div_pos hη (by positivity))
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ2] with h hh
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hh
    have hh_δ : |h| < δ / 2 := lt_of_lt_of_le hh (min_le_left _ _)
    have hh_η : |h| < η / (K + 1) := lt_of_lt_of_le hh (min_le_right _ _)
    simp only [smul_zero, sub_zero, intervalIntegral.integral_same]
    have hdiff_le : ∀ r ∈ uIoc t₀ (t₀ + h), ‖G (t₀ + h) r - G t₀ r‖ ≤ K * |h| := by
      intro r hr
      have hr_hi : r ≤ t₀ + δ := by
        have h1 : r ≤ max t₀ (t₀ + h) := (uIoc_subset_uIcc hr).2
        have h2 : max t₀ (t₀ + h) ≤ t₀ + δ :=
          max_le (by linarith) (by linarith [(abs_lt.mp hh_δ).2])
        exact h1.trans h2
      have hd_seg : ∀ s ∈ uIcc t₀ (t₀ + h),
          HasDerivWithinAt (fun s => G s r) (G' s r) (uIcc t₀ (t₀ + h)) s := by
        intro s hs
        have hs_in : s ∈ Ioo (t₀ - δ) (t₀ + δ) :=
          ⟨lt_of_lt_of_le (lt_min (by linarith) (by linarith [(abs_lt.mp hh_δ).1])) hs.1,
            lt_of_le_of_lt hs.2 (max_lt (by linarith) (by linarith [(abs_lt.mp hh_δ).2]))⟩
        have h34 := hage_ball hs_in hr_hi
        exact (hasDerivAt_duhRegIntegrand hc hν hV u₀ hε α (by linarith)).hasDerivWithinAt
      have hb_seg : ∀ s ∈ uIcc t₀ (t₀ + h), ‖G' s r‖ ≤ K := by
        intro s hs
        have hs_in : s ∈ Ioo (t₀ - δ) (t₀ + δ) :=
          ⟨lt_of_lt_of_le (lt_min (by linarith) (by linarith [(abs_lt.mp hh_δ).1])) hs.1,
            lt_of_le_of_lt hs.2 (max_lt (by linarith) (by linarith [(abs_lt.mp hh_δ).2]))⟩
        have h34 := hage_ball hs_in hr_hi
        exact hG'_bound (by linarith)
      have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd_seg hb_seg
        (convex_uIcc t₀ (t₀ + h)) left_mem_uIcc right_mem_uIcc
      simpa only [Real.norm_eq_abs, add_sub_cancel_left] using hmv
    have hint_le := intervalIntegral.norm_integral_le_of_norm_le_const hdiff_le
    have hKh : K * |h| ≤ η := by
      have hpos : 0 < K + 1 := by positivity
      have := (lt_div_iff₀ hpos).1 hh_η
      nlinarith [abs_nonneg h]
    calc ‖∫ r in t₀..(t₀ + h), (G (t₀ + h) r - G t₀ r)‖
        ≤ (K * |h|) * |t₀ + h - t₀| := hint_le
      _ = (K * |h|) * ‖h‖ := by rw [add_sub_cancel_left, Real.norm_eq_abs]
      _ ≤ η * ‖h‖ := mul_le_mul_of_nonneg_right hKh (norm_nonneg _)
  -- Combine Parts A, B1, B2 on `(t₀ - δ / 2, t₀ + δ / 2)`
  have hd_duh : HasDerivAt (fun t => ∫ r in (0 : ℝ)..t, G t r)
      ((∫ r in (0 : ℝ)..t₀, G' t₀ r) +
        P0 c (iterDHeatCLM hc α ε (fReg hc hν hV u₀ ε t₀))) t₀ := by
    have hd_sum := hd_partA.add ((hd_partB1.add hd_partB2).congr_deriv (add_zero _))
    refine hd_sum.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds (by linarith : t₀ - δ / 2 < t₀)
      (by linarith : t₀ < t₀ + δ / 2)] with t ht
    have ht_lo : 0 < t := by linarith [hδ_t0, ht.1]
    have ht_hi : t < 2 := by linarith [hδ_2t0, ht.2]
    have ht_ball : t ∈ Ioo (t₀ - δ) (t₀ + δ) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hi_0t0 : IntervalIntegrable (G t) volume 0 t₀ :=
      intervalIntegrable_duhRegIntegrand hc hν hV u₀ hε α t
        (by simp [ht₀.1.le]) (max_le zero_le_two ht₀.2.le) fun r hr => by
          rw [uIcc_of_le ht₀.1.le] at hr
          have h34 := hage_ball ht_ball (by linarith [hr.2] : r ≤ t₀ + δ)
          linarith
    have hi_t0t : IntervalIntegrable (G t) volume t₀ t :=
      intervalIntegrable_duhRegIntegrand hc hν hV u₀ hε α t
        (le_min ht₀.1.le ht_lo.le) (max_le ht₀.2.le ht_hi.le) fun r hr => by
          have hr_hi : r ≤ max t₀ t := (hr).2
          have hm_hi : max t₀ t ≤ t₀ + δ := max_le (by linarith) (by linarith [ht.2])
          have h34 := hage_ball ht_ball (hr_hi.trans hm_hi)
          linarith
    have hi_Gt0 : IntervalIntegrable (G t₀) volume t₀ t := by
      have hsub : uIcc t₀ t ⊆ uIcc (t₀ - δ / 2) (t₀ + δ / 2) := by
        rw [uIcc_of_le (by linarith : t₀ - δ / 2 ≤ t₀ + δ / 2)]
        exact uIcc_subset_Icc ⟨by linarith, by linarith⟩ ⟨ht.1.le, ht.2.le⟩
      exact (hGt0_cont_near.mono hsub).intervalIntegrable
    rw [← intervalIntegral.integral_add_adjacent_intervals hi_0t0 hi_t0t]
    simp only [Pi.add_apply]
    congr 1
    have hsplit : (fun r => G t r) = fun r => G t₀ r + (G t r - G t₀ r) := by
      funext r; abel
    rw [hsplit, intervalIntegral.integral_add hi_Gt0 (hi_t0t.sub hi_Gt0)]
  -- Identify `∫ r in 0..t₀, G' t₀ r` with `ν • (∫ G_{0::0::α} + ∫ G_{1::1::α})`
  have hG'_int_eq : (∫ r in (0 : ℝ)..t₀, G' t₀ r) =
      ν • ((∫ r in (0 : ℝ)..t₀, duhRegIntegrand hc hν hV u₀ ε (0 :: 0 :: α) t₀ r) +
        (∫ r in (0 : ℝ)..t₀, duhRegIntegrand hc hν hV u₀ ε (1 :: 1 :: α) t₀ r)) := by
    have hage0 : ∀ r ∈ uIcc (0 : ℝ) t₀, ε / 2 < ν * (t₀ - r) + ε := by
      rw [uIcc_of_le ht₀.1.le]
      intro r hr
      have : 0 ≤ ν * (t₀ - r) := mul_nonneg hν.le (sub_nonneg.mpr hr.2)
      linarith
    have i0 := intervalIntegrable_duhRegIntegrand hc hν hV u₀ hε (0 :: 0 :: α) t₀
      (by simp [ht₀.1.le]) (max_le zero_le_two ht₀.2.le) hage0
    have i1 := intervalIntegrable_duhRegIntegrand hc hν hV u₀ hε (1 :: 1 :: α) t₀
      (by simp [ht₀.1.le]) (max_le zero_le_two ht₀.2.le) hage0
    dsimp [G']
    rw [intervalIntegral.integral_smul, intervalIntegral.integral_add i0 i1]
  refine (hd_free.sub hd_duh).congr_deriv ?_
  rw [hG'_int_eq]
  unfold uReg
  simp only [smul_add, smul_sub]
  abel

end UnforcedLeray.Short.IIb.F8MildBoot

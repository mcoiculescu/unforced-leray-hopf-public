import UnforcedLeray.Lib.CylinderB.ModePairing

/-!
# CY13: the cylinder Liouville theorem in `H^{-1}(C_c)` (Riesz route, decision D15)


(§5 Layer 2, bypass BP7; decision D15 of the scoping README: the cylinder Liouville theorem is
built once, here, by the Riesz route). Manuscript: `paper/main.tex` line 14360, blueprint unit
B0935 (`unlabeled:14360:liouville`): an `L²`-based `D ∈ H^{-1}(C_c)` with `curl D = 0` and
`div D = 0` vanishes.

## Statement
`D = (D₁, D₂) ∈ Hneg c 0 1 × Hneg c 0 1`, i.e. two continuous functionals on the unweighted
`H¹(C_c)` (periodic weak derivatives, `Sob.cylinder c`). The distributional conditions are
tested on the periodic tests `φ` (`Sob.IsCylTest c`), embedded in `H¹` by `testH`:
`curl D (φ) = D₁(∂_η φ) − D₂(∂_q φ) = 0` and `div D (φ) = −(D₁(∂_q φ) + D₂(∂_η φ)) = 0`.

## Proof (BP7, without distributions on the cylinder)
By Riesz, `D_i = ⟨u_i, ·⟩_{H¹}` with `u_i ∈ H¹`, and `⟨u, φ⟩_{H¹} = ∫ u (1 − Δ)φ` for tests
(`inner_testH`). The two conditions become `∫ (1−Δ)φ · (∂_q u₂ − ∂_η u₁) = 0` and
`∫ (1−Δ)φ · (∂_q u₁ + ∂_η u₂) = 0`. On the `n`-th `q`-mode (`k = 2πn/c`), tested with
`cos(kq)ψ(η)`, `sin(kq)ψ(η)` (`ModePairing`), these are one-dimensional Helmholtz equations
`(1 + k² − ∂²) v = 0` with `v ∈ L²(ℝ)`, so `v = 0` (`OneD.eq_zero_of_helmholtz`). Hence on every
mode `A' = −ik B`, `B' = ik A` for the modes `A`, `B` of `u₁`, `u₂`; so `(k² − ∂²)A = 0`, and
`A = 0`, then `B' = 0` and `B = 0` (`OneD.eq_zero_of_helmholtz`, `OneD.eq_zero_of_deriv`).
Parseval (`ae_eq_zero_of_qMode`) gives `u₁ = u₂ = 0`.

## Main declarations
* `inner_testH`, `inner_testH_q`, `inner_testH_eta`;
* `mode_eta`, `mode_q`: weak derivatives on `q`-modes;
* `eq_zero_of_curl_div`: **CY13**.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Complex
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Cyl

variable {c : ℝ}

/-- The weight of the unweighted dual pairing. -/
abbrev ρ0 (c : ℝ) : Sob.Weight Plane := (ρwW c ^ (0 : ℝ)).inv

/-- The field of an element of `H¹`. -/
abbrev fld (u : H10 c) : Plane → ℝ := (Sob.W.value (Sob.cylinder c) (ρ0 c) ℝ ℝ 1 2 u : Plane → ℝ)

/-- A first-order component of an element of `H¹`. -/
abbrev cmp (α : Sob.Idx 2 1) (u : H10 c) : Plane → ℝ :=
  (Sob.W.deriv (Sob.cylinder c) (ρ0 c) ℝ ℝ 1 2 α u : Plane → ℝ)

theorem integral_wμ0 (F : Plane → ℝ) :
    ∫ x, F x ∂(Sob.wμ (Sob.cylinder c).μ (ρ0 c)) = ∫ z in cell c, F z :=
  congrArg (fun ν => ∫ x, F x ∂ν) (wμ_ρwW_zero_inv c)

theorem memLp_cmp (α : Sob.Idx 2 1) (u : H10 c) : MemLp (cmp α u) 2 (cellμ c) :=
  (wμ_ρwW_zero_inv c) ▸ Lp.memLp _

theorem memLp_fld (u : H10 c) : MemLp (fld u) 2 (cellμ c) :=
  (wμ_ρwW_zero_inv c) ▸ Lp.memLp _

theorem ae_cell_of_cylinder {P : Plane → Prop} (h : ∀ᵐ x ∂(Sob.cylinder c).μ, P x) :
    ∀ᵐ x ∂(cellμ c), P x := by
  rwa [cylinder_μ_eq] at h

theorem ae_cylinder_of_cell {P : Plane → Prop} (h : ∀ᵐ x ∂(cellμ c), P x) :
    ∀ᵐ x ∂(Sob.cylinder c).μ, P x := by
  rwa [cylinder_μ_eq]

/-- The `H¹` inner product as three `L²(cell)` pairings. -/
theorem inner_H10 (u v : H10 c) :
    inner ℝ u v = (∫ z in cell c, fld v z * fld u z) +
      (∫ z in cell c, cmp iQ v z * cmp iQ u z) + ∫ z in cell c, cmp iEta v z * cmp iEta u z := by
  rw [Sob.W.inner_eq, univ_idx_two_one, Finset.sum_insert, Finset.sum_insert,
    Finset.sum_singleton]
  · simp only [L2.inner_def, RCLike.inner_apply, conj_trivial]
    rw [integral_wμ0, integral_wμ0, integral_wμ0, ← add_assoc]
    rfl
  · simpa using idx_ne.2.2
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨idx_ne.1, idx_ne.2.1⟩

/-- The weak-derivative identity of `u ∈ H¹` against a test, in cell form. -/
theorem weak_identity (u : H10 c) {φ : Plane → ℝ} (hφ : Sob.IsCylTest c φ) (v : Plane)
    (α : Sob.Idx 2 1) (hα : (Sob.cylinder c).word α = [v]) :
    ∫ z in cell c, fderiv ℝ φ z v * fld u z = -∫ z in cell c, φ z * cmp α u z := by
  have h := (Sob.W.hasWeakDeriv u α).identity φ hφ
  rw [hα] at h
  simp only [Sob.iterDirDeriv_singleton, smul_eq_mul, List.length_singleton, pow_one,
    neg_one_mul, cylinder_integral] at h
  exact h

/-- **Riesz on tests**: `⟨u, φ⟩_{H¹} = ∫ (1 − Δ)φ · u`. -/
theorem inner_testH (hc : 0 < c) (u : H10 c) {φ : Plane → ℝ} (hφ : Sob.IsCylTest c φ) :
    inner ℝ u (testH hc hφ (ρ0 c) 1) = ∫ z in cell c, Lop φ z * fld u z := by
  rw [inner_H10]
  have hv : ∀ α : Sob.Idx 2 1, (Sob.W.deriv (Sob.cylinder c) (ρ0 c) ℝ ℝ 1 2 α
      (testH hc hφ (ρ0 c) 1) : Plane → ℝ) =ᵐ[volume.restrict (cell c)]
        Sob.iterDirDeriv ((Sob.cylinder c).word α) φ :=
    fun α => ae_cell_of_cylinder (coeFn_deriv_testH hc hφ (ρ0 c) 1 α)
  have e0 : ∫ z in cell c, fld (testH hc hφ (ρ0 c) 1) z * fld u z =
      ∫ z in cell c, φ z * fld u z := by
    refine integral_congr_ae ?_
    filter_upwards [hv Sob.Idx.zero] with z hz
    rw [show fld (testH hc hφ (ρ0 c) 1) z = _ from hz, word_zero, Sob.iterDirDeriv_nil]
  have hQ := (Sob.cylinder c).adm_iterDirDeriv hφ [((1 : ℝ), (0 : ℝ))]
  have hE := (Sob.cylinder c).adm_iterDirDeriv hφ [((0 : ℝ), (1 : ℝ))]
  have eQ : ∫ z in cell c, cmp iQ (testH hc hφ (ρ0 c) 1) z * cmp iQ u z =
      -∫ z in cell c, Sob.iterDirDeriv [((1 : ℝ), (0 : ℝ)), ((1 : ℝ), (0 : ℝ))] φ z * fld u z := by
    have h1 : ∫ z in cell c, cmp iQ (testH hc hφ (ρ0 c) 1) z * cmp iQ u z =
        ∫ z in cell c, Sob.iterDirDeriv [((1 : ℝ), (0 : ℝ))] φ z * cmp iQ u z := by
      refine integral_congr_ae ?_
      filter_upwards [hv iQ] with z hz
      rw [show cmp iQ (testH hc hφ (ρ0 c) 1) z = _ from hz, word_iQ]
    have h2 : ∫ z in cell c, Sob.iterDirDeriv [((1 : ℝ), (0 : ℝ)), ((1 : ℝ), (0 : ℝ))] φ z *
        fld u z = -∫ z in cell c, Sob.iterDirDeriv [((1 : ℝ), (0 : ℝ))] φ z * cmp iQ u z :=
      weak_identity u hQ (1, 0) iQ (word_iQ c)
    rw [h1, h2, neg_neg]
  have eE : ∫ z in cell c, cmp iEta (testH hc hφ (ρ0 c) 1) z * cmp iEta u z =
      -∫ z in cell c, Sob.iterDirDeriv [((0 : ℝ), (1 : ℝ)), ((0 : ℝ), (1 : ℝ))] φ z * fld u z := by
    have h1 : ∫ z in cell c, cmp iEta (testH hc hφ (ρ0 c) 1) z * cmp iEta u z =
        ∫ z in cell c, Sob.iterDirDeriv [((0 : ℝ), (1 : ℝ))] φ z * cmp iEta u z := by
      refine integral_congr_ae ?_
      filter_upwards [hv iEta] with z hz
      rw [show cmp iEta (testH hc hφ (ρ0 c) 1) z = _ from hz, word_iEta]
    have h2 : ∫ z in cell c, Sob.iterDirDeriv [((0 : ℝ), (1 : ℝ)), ((0 : ℝ), (1 : ℝ))] φ z *
        fld u z = -∫ z in cell c, Sob.iterDirDeriv [((0 : ℝ), (1 : ℝ))] φ z * cmp iEta u z :=
      weak_identity u hE (0, 1) iEta (word_iEta c)
    rw [h1, h2, neg_neg]
  rw [e0, eQ, eE]
  have i0 := integrableOn_test_mul hφ (memLp_fld u)
  have i1 := integrableOn_test_mul ((Sob.cylinder c).adm_iterDirDeriv hφ
    [((1 : ℝ), (0 : ℝ)), ((1 : ℝ), (0 : ℝ))]) (memLp_fld u)
  have i2 := integrableOn_test_mul ((Sob.cylinder c).adm_iterDirDeriv hφ
    [((0 : ℝ), (1 : ℝ)), ((0 : ℝ), (1 : ℝ))]) (memLp_fld u)
  have : (fun z => Lop φ z * fld u z) = fun z =>
      (φ z * fld u z - Sob.iterDirDeriv [((1 : ℝ), (0 : ℝ)), ((1 : ℝ), (0 : ℝ))] φ z * fld u z) -
        Sob.iterDirDeriv [((0 : ℝ), (1 : ℝ)), ((0 : ℝ), (1 : ℝ))] φ z * fld u z := by
    funext z; simp only [Lop]; ring
  have hs1 : ∫ z in cell c, (φ z * fld u z -
      Sob.iterDirDeriv [((1 : ℝ), (0 : ℝ)), ((1 : ℝ), (0 : ℝ))] φ z * fld u z) =
      (∫ z in cell c, φ z * fld u z) -
        ∫ z in cell c, Sob.iterDirDeriv [((1 : ℝ), (0 : ℝ)), ((1 : ℝ), (0 : ℝ))] φ z * fld u z :=
    integral_sub i0 i1
  have hs2 : ∫ z in cell c, ((φ z * fld u z -
      Sob.iterDirDeriv [((1 : ℝ), (0 : ℝ)), ((1 : ℝ), (0 : ℝ))] φ z * fld u z) -
        Sob.iterDirDeriv [((0 : ℝ), (1 : ℝ)), ((0 : ℝ), (1 : ℝ))] φ z * fld u z) =
      (∫ z in cell c, (φ z * fld u z -
        Sob.iterDirDeriv [((1 : ℝ), (0 : ℝ)), ((1 : ℝ), (0 : ℝ))] φ z * fld u z)) -
        ∫ z in cell c, Sob.iterDirDeriv [((0 : ℝ), (1 : ℝ)), ((0 : ℝ), (1 : ℝ))] φ z * fld u z :=
    integral_sub (i0.sub i1) i2
  rw [this, hs2, hs1]
  ring

/-- `⟨u, ∂_η φ⟩_{H¹} = −∫ (1 − Δ)φ · ∂_η u`. -/
theorem inner_testH_eta (hc : 0 < c) (u : H10 c) {φ : Plane → ℝ} (hφ : Sob.IsCylTest c φ) :
    inner ℝ u (testH hc (hφ.dirDeriv ((0 : ℝ), (1 : ℝ))) (ρ0 c) 1) =
      -∫ z in cell c, Lop φ z * cmp iEta u z := by
  rw [inner_testH, Lop_dir hφ]
  exact weak_identity u (isCylTest_Lop hφ) (0, 1) iEta (word_iEta c)

/-- `⟨u, ∂_q φ⟩_{H¹} = −∫ (1 − Δ)φ · ∂_q u`. -/
theorem inner_testH_q (hc : 0 < c) (u : H10 c) {φ : Plane → ℝ} (hφ : Sob.IsCylTest c φ) :
    inner ℝ u (testH hc (hφ.dirDeriv ((1 : ℝ), (0 : ℝ))) (ρ0 c) 1) =
      -∫ z in cell c, Lop φ z * cmp iQ u z := by
  rw [inner_testH, Lop_dir hφ]
  exact weak_identity u (isCylTest_Lop hφ) (1, 0) iQ (word_iQ c)

/-! ### Modes -/

/-- The `n`-th `q`-mode of a real cell function. -/
abbrev modeR (c : ℝ) (hc : 0 < c) (n : ℤ) (g : Plane → ℝ) : ℝ → ℂ :=
  qMode c hc n (fun z => (g z : ℂ))

theorem memLp_modeR (hc : 0 < c) (n : ℤ) {g : Plane → ℝ} (hg : MemLp g 2 (cellμ c)) :
    MemLp (modeR c hc n g) 2 volume :=
  memLp_qMode hc n (hg.ofReal (K := ℂ))

theorem integrable_modeR (hc : 0 < c) (n : ℤ) {g : Plane → ℝ} (hg : MemLp g 2 (cellμ c))
    {ψ : ℝ → ℝ} (hψ : OneD.Test ψ) : Integrable (fun η => ψ η • modeR c hc n g η) volume :=
  OneD.integrable_smul_of_test hψ (memLp_modeR hc n hg)

theorem pairC_eq' (hc : 0 < c) (n : ℤ) {g : Plane → ℝ} (hg : MemLp g 2 (cellμ c)) {ψ : ℝ → ℝ}
    (hψ : OneD.Test ψ) : pairC c n g ψ = (c : ℂ) * ∫ η, ψ η • modeR c hc n g η :=
  pairC_eq hc n hg hψ

theorem integral_mode_eq_of_pairC (hc : 0 < c) (n : ℤ) {g h : Plane → ℝ}
    (hg : MemLp g 2 (cellμ c)) (hh : MemLp h 2 (cellμ c)) {ψ : ℝ → ℝ} (hψ : OneD.Test ψ)
    {a : ℂ} (hp : pairC c n g ψ = a * pairC c n h ψ) :
    ∫ η, ψ η • modeR c hc n g η = a * ∫ η, ψ η • modeR c hc n h η := by
  rw [pairC_eq' hc n hg hψ, pairC_eq' hc n hh hψ] at hp
  have hc0 : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  have := hp
  rw [mul_left_comm] at this
  exact mul_left_cancel₀ hc0 this

/-- **Weak `η`-derivative on a mode**: `∫ ψ' u^(n) = −∫ ψ (∂_η u)^(n)`. -/
theorem mode_eta (hc : 0 < c) (u : H10 c) (n : ℤ) {ψ : ℝ → ℝ} (hψ : OneD.Test ψ) :
    ∫ η, deriv ψ η • modeR c hc n (fld u) η = -∫ η, ψ η • modeR c hc n (cmp iEta u) η := by
  have hd : Differentiable ℝ ψ := hψ.smooth.differentiable (by simp)
  have hcos := weak_identity u (isCylTest_cosTest hc n hψ) (0, 1) iEta (word_iEta c)
  have hsin := weak_identity u (isCylTest_sinTest hc n hψ) (0, 1) iEta (word_iEta c)
  have ec : (fun z => fderiv ℝ (cosTest (freq c n) ψ) z ((0 : ℝ), (1 : ℝ))) =
      cosTest (freq c n) (deriv ψ) := by
    rw [dir01_eq (differentiable_cosTest _ hd), partialEta_cosTest _ hd]
  have es : (fun z => fderiv ℝ (sinTest (freq c n) ψ) z ((0 : ℝ), (1 : ℝ))) =
      sinTest (freq c n) (deriv ψ) := by
    rw [dir01_eq (differentiable_sinTest _ hd), partialEta_sinTest _ hd]
  have hcos' : ∫ z in cell c, cosTest (freq c n) (deriv ψ) z * fld u z =
      -∫ z in cell c, cosTest (freq c n) ψ z * cmp iEta u z := by
    rw [← hcos, ← ec]
  have hsin' : ∫ z in cell c, sinTest (freq c n) (deriv ψ) z * fld u z =
      -∫ z in cell c, sinTest (freq c n) ψ z * cmp iEta u z := by
    rw [← hsin, ← es]
  have hp : pairC c n (fld u) (deriv ψ) = (-1 : ℂ) * pairC c n (cmp iEta u) ψ := by
    simp only [pairC, hcos', hsin']; push_cast; ring
  rw [pairC_eq' hc n (memLp_fld u) hψ.deriv, pairC_eq' hc n (memLp_cmp iEta u) hψ] at hp
  have hc0 : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  refine mul_left_cancel₀ hc0 ?_
  rw [hp]; ring

/-- **Weak `q`-derivative on a mode**: `∫ ψ (∂_q u)^(n) = i k_n ∫ ψ u^(n)`. -/
theorem mode_q (hc : 0 < c) (u : H10 c) (n : ℤ) {ψ : ℝ → ℝ} (hψ : OneD.Test ψ) :
    ∫ η, ψ η • modeR c hc n (cmp iQ u) η =
      (I * (freq c n : ℂ)) * ∫ η, ψ η • modeR c hc n (fld u) η := by
  have hd : Differentiable ℝ ψ := hψ.smooth.differentiable (by simp)
  have hcos := weak_identity u (isCylTest_cosTest hc n hψ) (1, 0) iQ (word_iQ c)
  have hsin := weak_identity u (isCylTest_sinTest hc n hψ) (1, 0) iQ (word_iQ c)
  have ec : (fun z => fderiv ℝ (cosTest (freq c n) ψ) z ((1 : ℝ), (0 : ℝ))) =
      fun z => -freq c n * sinTest (freq c n) ψ z := by
    rw [dir10_eq (differentiable_cosTest _ hd), partialQ_cosTest]
  have es : (fun z => fderiv ℝ (sinTest (freq c n) ψ) z ((1 : ℝ), (0 : ℝ))) =
      fun z => freq c n * cosTest (freq c n) ψ z := by
    rw [dir10_eq (differentiable_sinTest _ hd), partialQ_sinTest]
  have hcos' : -freq c n * ∫ z in cell c, sinTest (freq c n) ψ z * fld u z =
      -∫ z in cell c, cosTest (freq c n) ψ z * cmp iQ u z := by
    rw [← hcos, ← integral_const_mul]
    congr 1; funext z
    rw [show fderiv ℝ (cosTest (freq c n) ψ) z ((1 : ℝ), (0 : ℝ)) =
      -freq c n * sinTest (freq c n) ψ z from congrFun ec z]
    ring
  have hsin' : freq c n * ∫ z in cell c, cosTest (freq c n) ψ z * fld u z =
      -∫ z in cell c, sinTest (freq c n) ψ z * cmp iQ u z := by
    rw [← hsin, ← integral_const_mul]
    congr 1; funext z
    rw [show fderiv ℝ (sinTest (freq c n) ψ) z ((1 : ℝ), (0 : ℝ)) =
      freq c n * cosTest (freq c n) ψ z from congrFun es z]
    ring
  have hp : pairC c n (cmp iQ u) ψ = (I * (freq c n : ℂ)) * pairC c n (fld u) ψ := by
    have h1 : ∫ z in cell c, cosTest (freq c n) ψ z * cmp iQ u z =
        freq c n * ∫ z in cell c, sinTest (freq c n) ψ z * fld u z := by linarith
    have h2 : ∫ z in cell c, sinTest (freq c n) ψ z * cmp iQ u z =
        -(freq c n * ∫ z in cell c, cosTest (freq c n) ψ z * fld u z) := by linarith
    simp only [pairC, h1, h2]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  exact integral_mode_eq_of_pairC hc n (memLp_cmp iQ u) (memLp_fld u) hψ hp

/-! ### The Helmholtz step -/

/-- If `∫ (1 − Δ)φ · g = ∫ (1 − Δ)φ · h` for all tests, then every mode of `g − h` vanishes. -/
theorem mode_eq_of_Lop (hc : 0 < c) {g h : Plane → ℝ} (hg : MemLp g 2 (cellμ c))
    (hh : MemLp h 2 (cellμ c)) {s : ℝ}
    (H : ∀ φ : Plane → ℝ, Sob.IsCylTest c φ →
      ∫ z in cell c, Lop φ z * g z = s * ∫ z in cell c, Lop φ z * h z) (n : ℤ) :
    modeR c hc n g =ᵐ[volume] fun η => (s : ℂ) * modeR c hc n h η := by
  set k := freq c n
  set a : ℝ := Real.sqrt (1 + k ^ 2)
  have ha2 : a ^ 2 = 1 + k ^ 2 := Real.sq_sqrt (by positivity)
  have ha : a ≠ 0 := by
    intro h0; rw [h0] at ha2; nlinarith [sq_nonneg k]
  set v : ℝ → ℂ := fun η => modeR c hc n g η - (s : ℂ) * modeR c hc n h η
  have hv : MemLp v 2 volume :=
    (memLp_modeR hc n hg).sub ((memLp_modeR hc n hh).const_mul _)
  have key : v =ᵐ[volume] 0 := by
    refine OneD.eq_zero_of_helmholtz ha hv fun ψ hψ => ?_
    set ψt : ℝ → ℝ := fun y => (1 + k ^ 2) * ψ y - deriv (deriv ψ) y
    have hψt : OneD.Test ψt := (hψ.const_mul _).sub hψ.deriv.deriv
    have hcos := H _ (isCylTest_cosTest hc n hψ)
    have hsin := H _ (isCylTest_sinTest hc n hψ)
    rw [Lop_cosTest _ hψ] at hcos
    rw [Lop_sinTest _ hψ] at hsin
    have hp : pairC c n g ψt = (s : ℂ) * pairC c n h ψt := by
      simp only [pairC]
      rw [hcos, hsin]; push_cast; ring
    have hm := integral_mode_eq_of_pairC hc n hg hh hψt hp
    have e : (fun x => (a ^ 2 * ψ x - deriv (deriv ψ) x) • v x) =
        fun x => ψt x • modeR c hc n g x - (s : ℂ) * (ψt x • modeR c hc n h x) := by
      funext x
      simp only [v, ψt, ha2, Complex.real_smul]
      push_cast
      ring
    rw [e, integral_sub (integrable_modeR hc n hg hψt)
      ((integrable_modeR hc n hh hψt).const_mul _), integral_const_mul, hm, sub_self]
  filter_upwards [key] with η hη
  simpa [v, sub_eq_zero] using hη

/-! ### The theorem -/

/-- **CY13: the cylinder Liouville theorem** (B0935, tex 14360; BP7, D15). An `L²`-based
`D = (D₁, D₂) ∈ H^{-1}(C_c)²` with `curl D = 0` and `div D = 0` (tested on the periodic tests
`φ`, through `testH`) vanishes. -/
theorem eq_zero_of_curl_div (hc : 0 < c) (D : Hneg c 0 1 × Hneg c 0 1)
    (hcurl : ∀ (φ : Plane → ℝ) (hφ : Sob.IsCylTest c φ),
      D.1 (testH hc (hφ.dirDeriv ((0 : ℝ), (1 : ℝ))) (ρ0 c) 1) -
        D.2 (testH hc (hφ.dirDeriv ((1 : ℝ), (0 : ℝ))) (ρ0 c) 1) = 0)
    (hdiv : ∀ (φ : Plane → ℝ) (hφ : Sob.IsCylTest c φ),
      D.1 (testH hc (hφ.dirDeriv ((1 : ℝ), (0 : ℝ))) (ρ0 c) 1) +
        D.2 (testH hc (hφ.dirDeriv ((0 : ℝ), (1 : ℝ))) (ρ0 c) 1) = 0) :
    D = 0 := by
  set u₁ : H10 c := (InnerProductSpace.toDual ℝ (H10 c)).symm D.1
  set u₂ : H10 c := (InnerProductSpace.toDual ℝ (H10 c)).symm D.2
  have hD1 : ∀ x, D.1 x = inner ℝ u₁ x := fun x =>
    (InnerProductSpace.toDual_symm_apply (x := x) (y := D.1)).symm
  have hD2 : ∀ x, D.2 x = inner ℝ u₂ x := fun x =>
    (InnerProductSpace.toDual_symm_apply (x := x) (y := D.2)).symm
  -- the two first-order systems
  have C1 : ∀ φ : Plane → ℝ, Sob.IsCylTest c φ →
      ∫ z in cell c, Lop φ z * cmp iQ u₂ z = 1 * ∫ z in cell c, Lop φ z * cmp iEta u₁ z := by
    intro φ hφ
    have := hcurl φ hφ
    rw [hD1, hD2, inner_testH_eta hc u₁ hφ, inner_testH_q hc u₂ hφ] at this
    linarith
  have C2 : ∀ φ : Plane → ℝ, Sob.IsCylTest c φ →
      ∫ z in cell c, Lop φ z * cmp iQ u₁ z = (-1) * ∫ z in cell c, Lop φ z * cmp iEta u₂ z := by
    intro φ hφ
    have := hdiv φ hφ
    rw [hD1, hD2, inner_testH_q hc u₁ hφ, inner_testH_eta hc u₂ hφ] at this
    linarith
  -- every mode of `u₁`, `u₂` vanishes
  have hmodes : ∀ n : ℤ, modeR c hc n (fld u₁) =ᵐ[volume] 0 ∧
      modeR c hc n (fld u₂) =ᵐ[volume] 0 := by
    intro n
    set k := freq c n
    have M1 := mode_eq_of_Lop hc (memLp_cmp iQ u₂) (memLp_cmp iEta u₁) C1 n
    have M2 := mode_eq_of_Lop hc (memLp_cmp iQ u₁) (memLp_cmp iEta u₂) C2 n
    -- `∫ ψ' A = −ik ∫ ψ B` and `∫ ψ' B = ik ∫ ψ A`
    have EA : ∀ ψ : ℝ → ℝ, OneD.Test ψ →
        ∫ η, deriv ψ η • modeR c hc n (fld u₁) η =
          -((I * (k : ℂ)) * ∫ η, ψ η • modeR c hc n (fld u₂) η) := by
      intro ψ hψ
      rw [mode_eta hc u₁ n hψ, ← mode_q hc u₂ n hψ]
      congr 1
      refine integral_congr_ae ?_
      filter_upwards [M1] with η hη
      rw [hη]; push_cast; ring
    have EB : ∀ ψ : ℝ → ℝ, OneD.Test ψ →
        ∫ η, deriv ψ η • modeR c hc n (fld u₂) η =
          (I * (k : ℂ)) * ∫ η, ψ η • modeR c hc n (fld u₁) η := by
      intro ψ hψ
      rw [mode_eta hc u₂ n hψ, ← mode_q hc u₁ n hψ, ← integral_neg]
      refine integral_congr_ae ?_
      filter_upwards [M2] with η hη
      rw [hη]; push_cast; simp [smul_neg]
    have hA : modeR c hc n (fld u₁) =ᵐ[volume] 0 := by
      by_cases hk : k = 0
      · refine OneD.eq_zero_of_deriv (memLp_modeR hc n (memLp_fld u₁)) fun ψ hψ => ?_
        rw [EA ψ hψ, hk]; simp
      · refine OneD.eq_zero_of_helmholtz hk (memLp_modeR hc n (memLp_fld u₁)) fun ψ hψ => ?_
        have i1 := integrable_modeR hc n (memLp_fld u₁) hψ
        have i2 := integrable_modeR hc n (memLp_fld u₁) hψ.deriv.deriv
        have e : (fun x => (k ^ 2 * ψ x - deriv (deriv ψ) x) • modeR c hc n (fld u₁) x) =
            fun x => (k ^ 2 : ℂ) * (ψ x • modeR c hc n (fld u₁) x) -
              deriv (deriv ψ) x • modeR c hc n (fld u₁) x := by
          funext x; simp only [Complex.real_smul]; push_cast; ring
        rw [e, integral_sub (i1.const_mul _) i2, integral_const_mul, EA _ hψ.deriv, EB ψ hψ]
        have hI : (I * (k : ℂ)) * (I * (k : ℂ)) = -(k ^ 2 : ℂ) := by
          rw [mul_mul_mul_comm, Complex.I_mul_I]; push_cast; ring
        rw [← mul_assoc, hI]; ring
    have hB : modeR c hc n (fld u₂) =ᵐ[volume] 0 := by
      refine OneD.eq_zero_of_deriv (memLp_modeR hc n (memLp_fld u₂)) fun ψ hψ => ?_
      rw [EB ψ hψ, integral_congr_ae (g := fun _ => (0 : ℂ))
        (hA.mono fun η hη => by simp [hη]), integral_zero, mul_zero]
    exact ⟨hA, hB⟩
  -- Parseval: `u₁ = u₂ = 0`
  have hzero : ∀ u : H10 c, (∀ n : ℤ, modeR c hc n (fld u) =ᵐ[volume] 0) → u = 0 := by
    intro u hu
    have h0 := ae_eq_zero_of_qMode hc ((memLp_fld u).ofReal (K := ℂ)) hu
    have h1 : fld u =ᵐ[cellμ c] 0 := h0.mono fun z hz => by
      simpa using hz
    apply Sob.W.ext
    apply Lp.ext
    rw [Sob.ae_eq_wμ_iff]
    filter_upwards [ae_cylinder_of_cell h1,
      (Sob.ae_eq_wμ_iff (Sob.cylinder c).μ (ρ0 c)).mp
        (Lp.coeFn_zero ℝ 2 (Sob.wμ (Sob.cylinder c).μ (ρ0 c)))] with z hz hz'
    rw [map_zero, hz']
    exact hz
  have hu₁ : u₁ = 0 := hzero u₁ fun n => (hmodes n).1
  have hu₂ : u₂ = 0 := hzero u₂ fun n => (hmodes n).2
  refine Prod.ext (ContinuousLinearMap.ext fun x => ?_) (ContinuousLinearMap.ext fun x => ?_)
  · rw [hD1, hu₁, inner_zero_left]; rfl
  · rw [hD2, hu₂, inner_zero_left]; rfl

end UnforcedLeray.Cyl

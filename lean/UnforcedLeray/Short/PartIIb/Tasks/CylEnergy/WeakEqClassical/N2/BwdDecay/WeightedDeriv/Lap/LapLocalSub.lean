import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3_2_2_2
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedDeriv.Grad.BwdOpPd
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedDeriv.Grad.PdJointSmooth
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedDeriv.Grad.BwdOpMul
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedDeriv.Grad.BwdOpLin
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedDeriv.Grad.CutProps
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedDeriv.Grad.CutPlane
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedDeriv.Lap.HessAlg

/-!


Source: `the November 2 reference manuscript` SP 2100-2105.
Same scheme as the gradient leaf: `L(∂_k φ)`, `L(Δφ)` and `L(|∇φ|²)` are obtained by the
differentiated-equation rule `bwdOpPd` (twice), linearity `bwdOpLin` and the product rule
`bwdOpMul`; the pointwise inequality is `hessAlg`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.IIb

/-- Smooth slices of a jointly smooth family on the open interval. -/
theorem lls_slice (s t : ℝ) (U : ℝ → B0579.Plane → ℝ)
    (hU : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℝ × B0579.Plane => U z.1 z.2)
      (Icc s t ×ˢ univ))
    (r : ℝ) (hr : r ∈ Ioo s t) : ContDiff ℝ 4 (U r) := by
  refine contDiff_iff_contDiffAt.2 (fun y => ?_)
  have hG : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℝ × B0579.Plane => U z.1 z.2) (r, y) :=
    hU.contDiffAt (prod_mem_nhds (Icc_mem_nhds hr.1 hr.2) univ_mem)
  have hl : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y' : B0579.Plane => (r, y')) y :=
    (contDiff_const.prodMk contDiff_id).contDiffAt
  exact (hG.comp y hl).of_le (by simp)

theorem lls_pd_c3 (j : Fin 2) (g : B0579.Plane → ℝ) (hg : ContDiff ℝ 4 g) :
    ContDiff ℝ 3 (B0579.pd j g) :=
  bwdPdD_cd j g 3 4 (by norm_num) hg

theorem lls_pd_c2 (j : Fin 2) (g : B0579.Plane → ℝ) (hg : ContDiff ℝ 4 g) :
    ContDiff ℝ 2 (B0579.pd j g) :=
  bwdPdD_cd j g 2 4 (by norm_num) hg

theorem lls_lap2 (f : B0579.Plane → ℝ) (hf : ContDiff ℝ 4 f) : ContDiff ℝ 2 (lapP f) := by
  have h1 : ContDiff ℝ 2 (B0579.pd 0 (B0579.pd 0 f)) :=
    bwdPdD_cd 0 (B0579.pd 0 f) 2 3 (by norm_num) (lls_pd_c3 0 f hf)
  have h2 : ContDiff ℝ 2 (B0579.pd 1 (B0579.pd 1 f)) :=
    bwdPdD_cd 1 (B0579.pd 1 f) 2 3 (by norm_num) (lls_pd_c3 1 f hf)
  exact h1.add h2

theorem lls_pd_neg (j : Fin 2) (g : B0579.Plane → ℝ) (x : B0579.Plane)
    (hg : DifferentiableAt ℝ g x) :
    B0579.pd j (fun y => -g y) x = -B0579.pd j g x := by
  unfold B0579.pd
  have h : HasFDerivAt (fun y => -g y) (-fderiv ℝ g x) x := hg.hasFDerivAt.neg
  rw [h.fderiv]
  simp

theorem lls_pd_zero (j : Fin 2) (x : B0579.Plane) :
    B0579.pd j (fun _ : B0579.Plane => (0 : ℝ)) x = 0 := by
  simp [B0579.pd]

theorem lls_pd_zero_fn (j : Fin 2) :
    B0579.pd j (fun _ : B0579.Plane => (0 : ℝ)) = fun _ => 0 :=
  funext fun y => lls_pd_zero j y

theorem lls_zero_fn (ν : ℝ) (b0 b1 : ℝ → B0579.Plane → ℝ) (r : ℝ) (x : B0579.Plane) :
    BwdOpAt ν b0 b1 (fun _ _ => (0 : ℝ)) r x 0 := by
  have h1 : lapP (fun _ : B0579.Plane => (0 : ℝ)) x = 0 := by
    unfold lapP
    simp only [lls_pd_zero_fn, lls_pd_zero, add_zero]
  refine ⟨0, hasDerivAt_const r (0 : ℝ), ?_⟩
  simp only [h1, lls_pd_zero, mul_zero, add_zero, zero_add]

theorem lls_bwd_congr {ν : ℝ} {b0 b1 U U' : ℝ → B0579.Plane → ℝ} {r : ℝ} {x : B0579.Plane}
    {F : ℝ} (hU : ∀ r' x', U r' x' = U' r' x') (h : BwdOpAt ν b0 b1 U r x F) :
    BwdOpAt ν b0 b1 U' r x F := by
  have e : U = U' := funext fun r' => funext fun x' => hU r' x'
  subst e
  exact h

theorem lls_bwd_val {ν : ℝ} {b0 b1 U : ℝ → B0579.Plane → ℝ} {r : ℝ} {x : B0579.Plane}
    {F F' : ℝ} (e : F = F') (h : BwdOpAt ν b0 b1 U r x F) : BwdOpAt ν b0 b1 U r x F' := by
  subst e
  exact h

theorem lls_static (ν : ℝ) (b0 b1 : ℝ → B0579.Plane → ℝ) (ζ : B0579.Plane → ℝ) (r : ℝ)
    (x : B0579.Plane) :
    BwdOpAt ν b0 b1 (fun _ => ζ) r x
      (ν * lapP ζ x + (b0 r x * B0579.pd 0 ζ x + b1 r x * B0579.pd 1 ζ x)) :=
  ⟨0, hasDerivAt_const r (ζ x), by simp⟩

theorem lls_add {ν : ℝ} {b0 b1 U W : ℝ → B0579.Plane → ℝ} {r : ℝ} {x : B0579.Plane}
    {FU FW : ℝ} (hU : ContDiff ℝ 2 (U r)) (hW : ContDiff ℝ 2 (W r))
    (hUa : BwdOpAt ν b0 b1 U r x FU) (hWa : BwdOpAt ν b0 b1 W r x FW) :
    BwdOpAt ν b0 b1 (fun r x => U r x + W r x) r x (FU + FW) := by
  have h := bwdOpLin ν b0 b1 U W r x 1 FU FW hU hW hUa hWa
  have h2 : BwdOpAt ν b0 b1 (fun r x => 1 * U r x + W r x) r x (FU + FW) :=
    lls_bwd_val (by ring) h
  exact lls_bwd_congr (fun _ _ => by simp) h2

/-- The first-order coefficient `F_k = -(∂_k b_0 ∂_0 φ + ∂_k b_1 ∂_1 φ)` of the differentiated
equation. -/
def lsF (b0 b1 : ℝ → B0579.Plane → ℝ) (φ : ℝ → B0579.Plane → ℝ) (k : Fin 2) (r : ℝ)
    (x : B0579.Plane) : ℝ :=
  -(B0579.pd k (b0 r) x * B0579.pd 0 (φ r) x + B0579.pd k (b1 r) x * B0579.pd 1 (φ r) x)

theorem lsF_pd (b0 b1 : ℝ → B0579.Plane → ℝ) (φ : ℝ → B0579.Plane → ℝ) (k j : Fin 2) (r : ℝ)
    (x : B0579.Plane) (h0 : ContDiff ℝ 4 (b0 r)) (h1 : ContDiff ℝ 4 (b1 r))
    (hφ : ContDiff ℝ 4 (φ r)) :
    B0579.pd j (fun y => lsF b0 b1 φ k r y) x =
      -(B0579.pd j (B0579.pd k (b0 r)) x * B0579.pd 0 (φ r) x +
        B0579.pd k (b0 r) x * B0579.pd j (B0579.pd 0 (φ r)) x +
        (B0579.pd j (B0579.pd k (b1 r)) x * B0579.pd 1 (φ r) x +
          B0579.pd k (b1 r) x * B0579.pd j (B0579.pd 1 (φ r)) x)) := by
  have dA : DifferentiableAt ℝ (B0579.pd k (b0 r)) x :=
    (lls_pd_c3 k (b0 r) h0).differentiable (by norm_num) x
  have dB : DifferentiableAt ℝ (B0579.pd k (b1 r)) x :=
    (lls_pd_c3 k (b1 r) h1).differentiable (by norm_num) x
  have dP0 : DifferentiableAt ℝ (B0579.pd 0 (φ r)) x :=
    (lls_pd_c3 0 (φ r) hφ).differentiable (by norm_num) x
  have dP1 : DifferentiableAt ℝ (B0579.pd 1 (φ r)) x :=
    (lls_pd_c3 1 (φ r) hφ).differentiable (by norm_num) x
  have hsum := lapPMul_pd_add j (fun y => B0579.pd k (b0 r) y * B0579.pd 0 (φ r) y)
    (fun y => B0579.pd k (b1 r) y * B0579.pd 1 (φ r) y) x (dA.mul dP0) (dB.mul dP1)
  have hneg := lls_pd_neg j (fun y => B0579.pd k (b0 r) y * B0579.pd 0 (φ r) y +
    B0579.pd k (b1 r) y * B0579.pd 1 (φ r) y) x ((dA.mul dP0).add (dB.mul dP1))
  have hm0 := lapPMul_pd_mul j (B0579.pd k (b0 r)) (B0579.pd 0 (φ r)) x dA dP0
  have hm1 := lapPMul_pd_mul j (B0579.pd k (b1 r)) (B0579.pd 1 (φ r)) x dB dP1
  unfold lsF
  rw [hneg, hsum, hm0, hm1]
  ring

/-- Level one: the first derivative `∂_k φ` solves the differentiated equation. -/
theorem lls_lvl1 (ν s t : ℝ) (b0 b1 : ℝ → B0579.Plane → ℝ) (φ : ℝ → B0579.Plane → ℝ)
    (hφs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℝ × B0579.Plane => φ z.1 z.2)
      (Icc s t ×ˢ univ))
    (hb : ∀ r ∈ Ioo s t, ContDiff ℝ 4 (b0 r) ∧ ContDiff ℝ 4 (b1 r))
    (hpde : ∀ r ∈ Ioo s t, ∀ x : B0579.Plane, BwdOpAt ν b0 b1 φ r x 0)
    (k : Fin 2) (r : ℝ) (hr : r ∈ Ioo s t) (x : B0579.Plane) :
    BwdOpAt ν b0 b1 (fun r x => B0579.pd k (φ r) x) r x (lsF b0 b1 φ k r x) := by
  have h := bwdOpPd ν s t b0 b1 φ (fun _ _ => (0 : ℝ)) hφs
    (fun r' hr' => ⟨contDiff_const, ((hb r' hr').1).of_le (by norm_num),
      ((hb r' hr').2).of_le (by norm_num)⟩)
    (fun r' hr' x' => hpde r' hr' x') k r hr x
  obtain ⟨D, hD, hE⟩ := h
  refine ⟨D, hD, ?_⟩
  have hz := lls_pd_zero k x
  beta_reduce at hE ⊢
  unfold lsF
  linear_combination hE + hz

/-- Level two: the second derivative `∂_j∂_k φ` solves the twice differentiated equation. -/
theorem lls_lvl2 (ν s t : ℝ) (b0 b1 : ℝ → B0579.Plane → ℝ) (φ : ℝ → B0579.Plane → ℝ)
    (hφs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℝ × B0579.Plane => φ z.1 z.2)
      (Icc s t ×ˢ univ))
    (hb : ∀ r ∈ Ioo s t, ContDiff ℝ 4 (b0 r) ∧ ContDiff ℝ 4 (b1 r))
    (hpde : ∀ r ∈ Ioo s t, ∀ x : B0579.Plane, BwdOpAt ν b0 b1 φ r x 0)
    (k j : Fin 2) (r : ℝ) (hr : r ∈ Ioo s t) (x : B0579.Plane) :
    BwdOpAt ν b0 b1 (fun r x => B0579.pd j (B0579.pd k (φ r)) x) r x
      (-(B0579.pd j (B0579.pd k (b0 r)) x * B0579.pd 0 (φ r) x +
        B0579.pd k (b0 r) x * B0579.pd j (B0579.pd 0 (φ r)) x +
        (B0579.pd j (B0579.pd k (b1 r)) x * B0579.pd 1 (φ r) x +
          B0579.pd k (b1 r) x * B0579.pd j (B0579.pd 1 (φ r)) x)) -
        (B0579.pd j (b0 r) x * B0579.pd 0 (B0579.pd k (φ r)) x +
          B0579.pd j (b1 r) x * B0579.pd 1 (B0579.pd k (φ r)) x)) := by
  have hr4 : ContDiff ℝ 4 (φ r) := lls_slice s t φ hφs r hr
  have hU : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : ℝ × B0579.Plane => (fun r x => B0579.pd k (φ r) x) z.1 z.2) (Icc s t ×ˢ univ) :=
    pdJointSmooth s t φ k hφs
  have hFc : ∀ r' ∈ Ioo s t, ContDiff ℝ 1 ((fun r x => lsF b0 b1 φ k r x) r') ∧
      ContDiff ℝ 1 (b0 r') ∧ ContDiff ℝ 1 (b1 r') := by
    intro r' hr'
    have h4 := lls_slice s t φ hφs r' hr'
    have hb0 := (hb r' hr').1
    have hb1 := (hb r' hr').2
    refine ⟨?_, hb0.of_le (by norm_num), hb1.of_le (by norm_num)⟩
    unfold lsF
    exact (((bwdPdD_cd k (b0 r') 1 4 (by norm_num) hb0).mul
      (bwdPdD_cd 0 (φ r') 1 4 (by norm_num) h4)).add
      ((bwdPdD_cd k (b1 r') 1 4 (by norm_num) hb1).mul
      (bwdPdD_cd 1 (φ r') 1 4 (by norm_num) h4))).neg
  have h := bwdOpPd ν s t b0 b1 (fun r x => B0579.pd k (φ r) x) (fun r x => lsF b0 b1 φ k r x)
    hU hFc (fun r' hr' x' => lls_lvl1 ν s t b0 b1 φ hφs hb hpde k r' hr' x') j r hr x
  obtain ⟨D, hD, hE⟩ := h
  refine ⟨D, hD, ?_⟩
  have hx := lsF_pd b0 b1 φ k j r x (hb r hr).1 (hb r hr).2 hr4
  beta_reduce at hE ⊢
  rw [hx] at hE
  linear_combination hE

/-- The main leaf. -/
theorem lapLocalSub : UnforcedLeray.Short.IIb.LapLocalSub := by
  intro ν c s t V v ψ φ hν hV hD hφ
  obtain ⟨Cθ, hC0, hCc⟩ := cutProps.2.2.2.2
  have hν0 : ν ≠ 0 := hν.ne'
  have h2ν : (0 : ℝ) < 2 * ν := by linarith
  have hN1 : 0 ≤ 32 * V ^ 2 + 2 + 6 * ν * Cθ + 2 * V + 2 * V * Cθ := by
    nlinarith [mul_nonneg hν.le hC0, mul_nonneg hV hC0, sq_nonneg V]
  obtain ⟨mu, hmu_def⟩ : ∃ m : ℝ,
      m = (32 * V ^ 2 + 2 + 6 * ν * Cθ + 2 * V + 2 * V * Cθ) / (2 * ν) := ⟨_, rfl⟩
  have hmu0 : 0 ≤ mu := by rw [hmu_def]; exact div_nonneg hN1 h2ν.le
  have hmu_eq : 2 * ν * mu = 32 * V ^ 2 + 2 + 6 * ν * Cθ + 2 * V + 2 * V * Cθ := by
    rw [hmu_def]; field_simp
  obtain ⟨kap, hkap_def⟩ : ∃ m : ℝ, m = (16 * V ^ 2 + 4 * V * mu) / (2 * ν) := ⟨_, rfl⟩
  have hkap0 : 0 ≤ kap := by
    rw [hkap_def]
    exact div_nonneg (by nlinarith [mul_nonneg hV hmu0, sq_nonneg V]) h2ν.le
  have hkap_eq : 2 * ν * kap = 16 * V ^ 2 + 4 * V * mu := by
    rw [hkap_def]; field_simp
  refine ⟨mu, kap, hmu0, hkap0, fun η0 r hr x => ?_⟩
  have hrI : r ∈ Icc s t := Ioo_subset_Icc_self hr
  have hr4 : ContDiff ℝ 4 (φ r) := lls_slice s t φ hφ.smooth r hr
  have hr2 : ContDiff ℝ 2 (φ r) := hr4.of_le (by norm_num)
  have hb : ∀ r' ∈ Ioo s t, ContDiff ℝ 4 ((fun r x => v r x 0) r') ∧
      ContDiff ℝ 4 ((fun r x => v r x 1) r') :=
    fun r' hr' => ⟨(hD.1 r' (Ioo_subset_Icc_self hr') 0).of_le (by simp),
      (hD.1 r' (Ioo_subset_Icc_self hr') 1).of_le (by simp)⟩
  have hpde : ∀ r' ∈ Ioo s t, ∀ x' : B0579.Plane,
      BwdOpAt ν (fun r x => v r x 0) (fun r x => v r x 1) φ r' x' 0 := by
    intro r' hr' x'
    refine ⟨-(ν * lapP (φ r') x' + (v r' x' 0 * B0579.pd 0 (φ r') x' +
      v r' x' 1 * B0579.pd 1 (φ r') x')), hφ.pde r' hr' x', ?_⟩
    beta_reduce
    ring
  -- the Laplacian `Δφ`
  have hL0 := lls_lvl2 ν s t (fun r x => v r x 0) (fun r x => v r x 1) φ hφ.smooth hb hpde
    0 0 r hr x
  have hL1 := lls_lvl2 ν s t (fun r x => v r x 0) (fun r x => v r x 1) φ hφ.smooth hb hpde
    1 1 r hr x
  have hw0 : ContDiff ℝ 2 (B0579.pd 0 (B0579.pd 0 (φ r))) :=
    bwdPdD_cd 0 (B0579.pd 0 (φ r)) 2 3 (by norm_num) (lls_pd_c3 0 (φ r) hr4)
  have hw1 : ContDiff ℝ 2 (B0579.pd 1 (B0579.pd 1 (φ r))) :=
    bwdPdD_cd 1 (B0579.pd 1 (φ r)) 2 3 (by norm_num) (lls_pd_c3 1 (φ r) hr4)
  have hLapA := bwdOpLin ν (fun r x => v r x 0) (fun r x => v r x 1)
    (fun r x => B0579.pd 0 (B0579.pd 0 (φ r)) x) (fun r x => B0579.pd 1 (B0579.pd 1 (φ r)) x)
    r x 1 _ _ hw0 hw1 hL0 hL1
  have hLap : BwdOpAt ν (fun r x => v r x 0) (fun r x => v r x 1)
      (fun r x => lapP (φ r) x) r x _ :=
    lls_bwd_congr (fun r' x' => by simp only [lapP, one_mul]) hLapA
  have hLL : ContDiff ℝ 2 (lapP (φ r)) := lls_lap2 (φ r) hr4
  -- the squared Laplacian
  have hSq := bwdOpMul ν (fun r x => v r x 0) (fun r x => v r x 1)
    (fun r x => lapP (φ r) x) (fun r x => lapP (φ r) x) r x _ _ hLL hLL hLap hLap
  -- the cutoff times the squared Laplacian
  have hζc : ContDiff ℝ 2 (cutζ η0) :=
    (cutProps.1.of_le (by simp)).comp (contDiff_snd.sub contDiff_const)
  have hζs := lls_static ν (fun r x => v r x 0) (fun r x => v r x 1) (cutζ η0) r x
  have hA := bwdOpMul ν (fun r x => v r x 0) (fun r x => v r x 1) (fun _ => cutζ η0)
    (fun r x => lapP (φ r) x * lapP (φ r) x) r x _ _ hζc (hLL.mul hLL) hζs hSq
  -- the gradient terms
  have hS0 := bwdOpMul ν (fun r x => v r x 0) (fun r x => v r x 1)
    (fun r x => B0579.pd 0 (φ r) x) (fun r x => B0579.pd 0 (φ r) x) r x _ _
    (lls_pd_c2 0 (φ r) hr4) (lls_pd_c2 0 (φ r) hr4)
    (lls_lvl1 ν s t (fun r x => v r x 0) (fun r x => v r x 1) φ hφ.smooth hb hpde 0 r hr x)
    (lls_lvl1 ν s t (fun r x => v r x 0) (fun r x => v r x 1) φ hφ.smooth hb hpde 0 r hr x)
  have hS1 := bwdOpMul ν (fun r x => v r x 0) (fun r x => v r x 1)
    (fun r x => B0579.pd 1 (φ r) x) (fun r x => B0579.pd 1 (φ r) x) r x _ _
    (lls_pd_c2 1 (φ r) hr4) (lls_pd_c2 1 (φ r) hr4)
    (lls_lvl1 ν s t (fun r x => v r x 0) (fun r x => v r x 1) φ hφ.smooth hb hpde 1 r hr x)
    (lls_lvl1 ν s t (fun r x => v r x 0) (fun r x => v r x 1) φ hφ.smooth hb hpde 1 r hr x)
  have hGSc : ContDiff ℝ 2 (fun x' => B0579.pd 0 (φ r) x' * B0579.pd 0 (φ r) x' +
      B0579.pd 1 (φ r) x' * B0579.pd 1 (φ r) x') :=
    ((lls_pd_c2 0 (φ r) hr4).mul (lls_pd_c2 0 (φ r) hr4)).add
      ((lls_pd_c2 1 (φ r) hr4).mul (lls_pd_c2 1 (φ r) hr4))
  have hGS := lls_add (U := fun r x => B0579.pd 0 (φ r) x * B0579.pd 0 (φ r) x)
    (W := fun r x => B0579.pd 1 (φ r) x * B0579.pd 1 (φ r) x)
    ((lls_pd_c2 0 (φ r) hr4).mul (lls_pd_c2 0 (φ r) hr4))
    ((lls_pd_c2 1 (φ r) hr4).mul (lls_pd_c2 1 (φ r) hr4)) hS0 hS1
  -- the quadratic term `|φ|²`
  have hPP := bwdOpMul ν (fun r x => v r x 0) (fun r x => v r x 1) φ φ r x 0 0 hr2 hr2
    (hpde r hr x) (hpde r hr x)
  have hKP := bwdOpLin ν (fun r x => v r x 0) (fun r x => v r x 1)
    (fun r x => φ r x * φ r x) (fun _ _ => (0 : ℝ)) r x kap _ 0 (hr2.mul hr2) contDiff_const
    hPP (lls_zero_fn ν (fun r x => v r x 0) (fun r x => v r x 1) r x)
  have hKPc : ContDiff ℝ 2 (fun x' => kap * (φ r x' * φ r x') + (0 : ℝ)) :=
    (contDiff_const.mul (hr2.mul hr2)).add contDiff_const
  -- the Bernstein combination `μ|∇φ|² + κ φ²`
  have hMG := bwdOpLin ν (fun r x => v r x 0) (fun r x => v r x 1)
    (fun r x => B0579.pd 0 (φ r) x * B0579.pd 0 (φ r) x + B0579.pd 1 (φ r) x * B0579.pd 1 (φ r) x)
    (fun r x => kap * (φ r x * φ r x) + (0 : ℝ)) r x mu _ _ hGSc hKPc hGS hKP
  -- the localized sum
  have hMGc : ContDiff ℝ 2 (fun x' => mu * (B0579.pd 0 (φ r) x' * B0579.pd 0 (φ r) x' +
      B0579.pd 1 (φ r) x' * B0579.pd 1 (φ r) x') + (kap * (φ r x' * φ r x') + (0 : ℝ))) :=
    (contDiff_const.mul hGSc).add hKPc
  have hFa := bwdOpLin ν (fun r x => v r x 0) (fun r x => v r x 1) _ _ r x 1 _ _
    (by exact hζc.mul (hLL.mul hLL)) (by exact hMGc) hA hMG
  have hfin : BwdOpAt ν (fun r x => v r x 0) (fun r x => v r x 1) (lapZ mu kap η0 φ) r x _ :=
    lls_bwd_congr (fun r' x' => by simp only [lapZ, lapSq, gradSq]; ring) hFa
  refine ⟨_, ?_, hfin⟩
  -- pointwise nonnegativity
  have hζ0 : 0 ≤ cutζ η0 x := (cutProps.2.2.1 (x.2 - η0)).1
  have hζ1 : cutζ η0 x ≤ 1 := (cutProps.2.2.1 (x.2 - η0)).2
  have hz := cutPlane η0 x
  have hZ : B0579.pd 0 (cutζ η0) x ^ 2 + B0579.pd 1 (cutζ η0) x ^ 2 ≤ Cθ * cutζ η0 x := by
    have h1 := (hCc (x.2 - η0)).1
    rw [hz.1, hz.2.1]
    unfold cutζ
    nlinarith [h1]
  have hlz : |lapP (cutζ η0) x| ≤ Cθ := by
    rw [hz.2.2]
    exact (hCc (x.2 - η0)).2
  have hD0 := hD.2 r hrI x 0
  have hD1 := hD.2 r hrI x 1
  have hmu_le : 32 * V ^ 2 + 2 + 6 * ν * Cθ + 2 * V + 2 * V * Cθ ≤ 2 * ν * mu :=
    le_of_eq hmu_eq.symm
  have hkap_le : 16 * V ^ 2 + 4 * V * mu ≤ 2 * ν * kap := le_of_eq hkap_eq.symm
  have key := hessAlg ν V Cθ mu kap (cutζ η0 x) (B0579.pd 0 (cutζ η0) x)
    (B0579.pd 1 (cutζ η0) x) (lapP (cutζ η0) x) (v r x 0) (v r x 1)
    (B0579.pd 0 (fun y => v r y 0) x) (B0579.pd 0 (fun y => v r y 1) x)
    (B0579.pd 1 (fun y => v r y 0) x) (B0579.pd 1 (fun y => v r y 1) x)
    (B0579.pd 0 (B0579.pd 0 (fun y => v r y 0)) x) (B0579.pd 0 (B0579.pd 0 (fun y => v r y 1)) x)
    (B0579.pd 1 (B0579.pd 1 (fun y => v r y 0)) x) (B0579.pd 1 (B0579.pd 1 (fun y => v r y 1)) x)
    (B0579.pd 0 (φ r) x) (B0579.pd 1 (φ r) x)
    (B0579.pd 0 (B0579.pd 0 (φ r)) x) (B0579.pd 0 (B0579.pd 1 (φ r)) x)
    (B0579.pd 1 (B0579.pd 0 (φ r)) x) (B0579.pd 1 (B0579.pd 1 (φ r)) x)
    (B0579.pd 0 (lapP (φ r)) x) (B0579.pd 1 (lapP (φ r)) x)
    hν hV hC0 hζ0 hζ1 hZ hlz hD0.1 hD1.1 (hD0.2.1 0) (hD1.2.1 0) (hD0.2.1 1) (hD1.2.1 1)
    (hD0.2.2 0 0) (hD1.2.2 0 0) (hD0.2.2 1 1) (hD1.2.2 1 1) hmu_le hkap_le
  have hLP : lapP (φ r) x = B0579.pd 0 (B0579.pd 0 (φ r)) x + B0579.pd 1 (B0579.pd 1 (φ r)) x :=
    rfl
  have hPW0 := lapPMul_pd_mul 0 (lapP (φ r)) (lapP (φ r)) x
    (hLL.differentiable (by norm_num) x) (hLL.differentiable (by norm_num) x)
  have hPW1 := lapPMul_pd_mul 1 (lapP (φ r)) (lapP (φ r)) x
    (hLL.differentiable (by norm_num) x) (hLL.differentiable (by norm_num) x)
  convert key using 1
  simp only [lsF, hLP, hPW0, hPW1]
  ring

end UnforcedLeray.Short.IIb

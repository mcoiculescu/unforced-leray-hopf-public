import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Continuity.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Continuity.Lam.MellinCont
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Continuity.Lam.AZeroLip
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AsymMu
import UnforcedLeray.Short.PartIIIb.Concrete.AffineEnvelope.Envelope

/-!
# The leaf `LamCont`: `Λ_{μ,ν}` is norm continuous in `μ` (source 4812-4815, 5918-5920)

Source of record: `the November 2 reference manuscript` (73 pages).

On the window the pinned `LamOp μ` is `A ↦ K₀(μ) Re[w(μ) a₀(μ, B_{μ,ν}[ιA])]` with
`K₀(μ) = -(3π/16)ε³ν^{5+2μ}`, `w(μ) = iN_ν 𝒥(μ)`.  Three ingredients:

* `K₀` is continuous (explicit);
* `𝒥` is continuous on `(-3/2, ∞)` (`planar_continuousAt_mellinJ`, dominated convergence);
* `μ ↦ a₀(B_{μ,ν}[A])` is Lipschitz on `[0,1]` uniformly in `M(A)` (`aZero_lip`), and
  `M(ιA) ≤ C_env ‖A‖` (source 5089-5091).

Then `‖LamOp μ - LamOp μ₀‖ ≤ g(μ)` with `g` continuous, `g(μ₀) = 0`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

/-- Norm continuity of `μ ↦ LamOp μ` on a subset `W ⊆ [0,1]` where the pins exist and `𝒥` is
continuous. -/
theorem lamOp_continuousOn (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel)
    (hχ : IsSourceCutoffC K.χf) (has : 0 ≤ K.as) (W : Set ℝ) (hW : W ⊆ Icc 0 1)
    (hpin : ∀ μ ∈ W, ∃ l : AffSp K.as →L[ℝ] ℝ, ∀ A, l A =
      LamFun Pl.eigenvalue Pl.kappa Pl.strainCoupling (planarJ Pl) L.ε L.ν μ K.χf
        (affIota K.as A))
    (hJ : ∀ μ ∈ W, ContinuousAt Pl.mellinJ μ) :
    ContinuousOn (fun μ => LamOp Pl K L μ) W := by
  intro μ0 hμ0
  have hν : 0 < L.ν := L.ν_pos
  set lam := Pl.eigenvalue
  set κ := Pl.kappa
  set ell := Pl.strainCoupling
  set ν := L.ν with hνdef
  set k : ℝ → ℝ := fun μ => -(3 * Real.pi / 16) * L.ε ^ 3 * ν ^ (5 + 2 * μ) with hk
  set w : ℝ → ℂ := fun μ => Complex.I * Nnu lam κ ν * Pl.mellinJ μ with hw
  set a : ℝ → AffSp K.as → ℂ := fun μ A =>
    aZero lam ell (μ : ℂ) (Bmat ν μ K.χf (affIota K.as A)) with ha
  have hform : ∀ μ A, LamFun lam κ ell (planarJ Pl) L.ε ν μ K.χf (affIota K.as A) =
      k μ * (w μ * a μ A).re := fun μ A => rfl
  have hspec : ∀ μ ∈ W, ∀ A, LamOp Pl K L μ A = k μ * (w μ * a μ A).re := by
    intro μ hμ A
    have h := Classical.epsilon_spec (hpin μ hμ)
    rw [← hform]
    exact h A
  -- constants
  obtain ⟨C, -, hC⟩ := affM_le_norm_of (affMEnvelope K.χf hχ)
  set Cenv : ℝ := max (C * Real.exp (1.1 * K.as / ν)) 0 with hCenv
  have hCenv0 : 0 ≤ Cenv := le_max_right _ _
  have henv : ∀ A : AffSp K.as, affM ν K.χf (affIota K.as A) ≤ Cenv * ‖A‖ := by
    intro A
    refine (hC K.as ν (fun A => affIota K.as A) has hν (affIota_mem K.as)
      (fun A => (affNorm_affIota K.as A).le) A).trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  have hμ0W := hW hμ0
  obtain ⟨Cb, hCb⟩ := aZeroBmatBound K.as K.χf hχ lam ell ν μ0 hν hμ0W.1
  set Cb' : ℝ := max Cb 0 with hCb'
  have hCb'0 : 0 ≤ Cb' := le_max_right _ _
  obtain ⟨Lp, hLp0, hLip⟩ := aZero_lip (as := K.as) hχ lam ell hν
  set g : ℝ → ℝ := fun μ => Cenv * (|k μ - k μ0| * ‖w μ0‖ * Cb' + |k μ| * ‖w μ - w μ0‖ * Cb' +
    |k μ| * ‖w μ‖ * (Lp * |μ - μ0|)) with hg
  have hg0 : ∀ μ, 0 ≤ g μ := by
    intro μ
    rw [hg]
    positivity
  have hbound : ∀ μ ∈ W, ‖LamOp Pl K L μ - LamOp Pl K L μ0‖ ≤ g μ := by
    intro μ hμ
    have hμW := hW hμ
    refine ContinuousLinearMap.opNorm_le_bound _ (hg0 μ) fun A => ?_
    rw [ContinuousLinearMap.sub_apply, hspec μ hμ, hspec μ0 hμ0, Real.norm_eq_abs]
    set M := affM ν K.χf (affIota K.as A) with hM
    have hM0 : 0 ≤ M := affM_nonneg _ _ _
    have hMe : M ≤ Cenv * ‖A‖ := henv A
    have ha0 : ‖a μ0 A‖ ≤ Cb' * M :=
      (hCb _ (affIota_mem K.as A)).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hM0)
    have ha1 : ‖a μ A - a μ0 A‖ ≤ Lp * |μ - μ0| * M :=
      hLip μ μ0 hμW.1 hμW.2 hμ0W.1 hμ0W.2 _ (affIota_mem K.as A)
    have hdec : k μ * (w μ * a μ A).re - k μ0 * (w μ0 * a μ0 A).re =
        (k μ - k μ0) * (w μ0 * a μ0 A).re + k μ * ((w μ - w μ0) * a μ0 A).re +
          k μ * (w μ * (a μ A - a μ0 A)).re := by
      simp only [sub_mul, mul_sub, Complex.sub_re]
      ring
    have hre : ∀ z : ℂ, |z.re| ≤ ‖z‖ := fun z => Complex.abs_re_le_norm z
    have t1 : |(k μ - k μ0) * (w μ0 * a μ0 A).re| ≤ |k μ - k μ0| * ‖w μ0‖ * (Cb' * M) := by
      rw [abs_mul]
      calc |k μ - k μ0| * |(w μ0 * a μ0 A).re| ≤ |k μ - k μ0| * ‖w μ0 * a μ0 A‖ :=
            mul_le_mul_of_nonneg_left (hre _) (abs_nonneg _)
        _ ≤ |k μ - k μ0| * (‖w μ0‖ * (Cb' * M)) := by
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_left ha0 (norm_nonneg _)
        _ = _ := by ring
    have t2 : |k μ * ((w μ - w μ0) * a μ0 A).re| ≤ |k μ| * ‖w μ - w μ0‖ * (Cb' * M) := by
      rw [abs_mul]
      calc |k μ| * |((w μ - w μ0) * a μ0 A).re| ≤ |k μ| * ‖(w μ - w μ0) * a μ0 A‖ :=
            mul_le_mul_of_nonneg_left (hre _) (abs_nonneg _)
        _ ≤ |k μ| * (‖w μ - w μ0‖ * (Cb' * M)) := by
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_left ha0 (norm_nonneg _)
        _ = _ := by ring
    have t3 : |k μ * (w μ * (a μ A - a μ0 A)).re| ≤ |k μ| * ‖w μ‖ * (Lp * |μ - μ0| * M) := by
      rw [abs_mul]
      calc |k μ| * |(w μ * (a μ A - a μ0 A)).re| ≤ |k μ| * ‖w μ * (a μ A - a μ0 A)‖ :=
            mul_le_mul_of_nonneg_left (hre _) (abs_nonneg _)
        _ ≤ |k μ| * (‖w μ‖ * (Lp * |μ - μ0| * M)) := by
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_left ha1 (norm_nonneg _)
        _ = _ := by ring
    rw [hdec]
    refine (abs_add_three _ _ _).trans ?_
    have hsum : |k μ - k μ0| * ‖w μ0‖ * (Cb' * M) + |k μ| * ‖w μ - w μ0‖ * (Cb' * M) +
        |k μ| * ‖w μ‖ * (Lp * |μ - μ0| * M) =
        (|k μ - k μ0| * ‖w μ0‖ * Cb' + |k μ| * ‖w μ - w μ0‖ * Cb' +
          |k μ| * ‖w μ‖ * (Lp * |μ - μ0|)) * M := by ring
    have hfac : 0 ≤ |k μ - k μ0| * ‖w μ0‖ * Cb' + |k μ| * ‖w μ - w μ0‖ * Cb' +
          |k μ| * ‖w μ‖ * (Lp * |μ - μ0|) := by positivity
    calc _ ≤ |k μ - k μ0| * ‖w μ0‖ * (Cb' * M) + |k μ| * ‖w μ - w μ0‖ * (Cb' * M) +
        |k μ| * ‖w μ‖ * (Lp * |μ - μ0| * M) := by linarith
      _ = _ := hsum
      _ ≤ (|k μ - k μ0| * ‖w μ0‖ * Cb' + |k μ| * ‖w μ - w μ0‖ * Cb' +
          |k μ| * ‖w μ‖ * (Lp * |μ - μ0|)) * (Cenv * ‖A‖) :=
        mul_le_mul_of_nonneg_left hMe hfac
      _ = g μ * ‖A‖ := by rw [hg]; ring
  -- continuity of g at μ0, with g μ0 = 0
  have hkc : ContinuousAt k μ0 := by
    refine continuousAt_const.mul ?_
    exact continuousAt_const.rpow (continuousAt_const.add (continuousAt_const.mul continuousAt_id))
      (Or.inl hν.ne')
  have hwc : ContinuousAt w μ0 := continuousAt_const.mul (hJ μ0 hμ0)
  have hgc : ContinuousAt g μ0 := by
    rw [hg]
    refine continuousAt_const.mul ?_
    have h1 : ContinuousAt (fun μ => |k μ - k μ0|) μ0 := (hkc.sub continuousAt_const).abs
    have h2 : ContinuousAt (fun μ => ‖w μ - w μ0‖) μ0 := (hwc.sub continuousAt_const).norm
    have h3 : ContinuousAt (fun μ => |k μ|) μ0 := hkc.abs
    have h4 : ContinuousAt (fun μ => ‖w μ‖) μ0 := hwc.norm
    have h5 : ContinuousAt (fun μ : ℝ => Lp * |μ - μ0|) μ0 :=
      continuousAt_const.mul (continuousAt_id.sub continuousAt_const).abs
    exact (((h1.mul continuousAt_const).mul continuousAt_const).add
      ((h3.mul h2).mul continuousAt_const)).add ((h3.mul h4).mul h5)
  have hgz : g μ0 = 0 := by simp [hg]
  have hT : Tendsto g (𝓝[W] μ0) (𝓝 0) := by
    rw [← hgz]
    exact hgc.tendsto.mono_left nhdsWithin_le_nhds
  exact tendsto_iff_norm_sub_tendsto_zero.2
    (squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      (eventually_nhdsWithin_of_forall hbound) hT)

/-- **`LamCont`** on the concrete sequence (source 4812-4815, 5918-5920, 5944-5947). -/
theorem SeqData.lamCont (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) : D.LamCont := by
  filter_upwards [hst.pins, mu_eventually_mem D hst.omega_ne hst.sigma_pos hst.sigma_lt]
    with n hp hn
  refine lamOp_continuousOn D.Pl D.K (D.level n) hst.chiF hst.as_pos.le (D.win n) ?_ ?_ ?_
  · rintro _ ⟨z, hz, rfl⟩
    have h := hn z hz
    have := hst.sigma_pos
    have := hst.sigma_lt
    constructor <;> linarith [h.1, h.2]
  · rintro _ ⟨z, hz, rfl⟩
    exact (hp z hz).lam
  · rintro μ hμ
    have : 0 ≤ μ := by
      obtain ⟨z, hz, rfl⟩ := hμ
      have h := hn z hz
      have := hst.sigma_pos
      linarith [h.1]
    exact planar_continuousAt_mellinJ hst.planar (by linarith)

end UnforcedLeray.Short.PartIIIb.Concrete

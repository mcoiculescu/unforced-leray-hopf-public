import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Continuity.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Continuity.Lj.AmbientDiff
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.N0
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AsymMu

/-!
# The leaf `LjCont`: `𝓛` is norm continuous in `μ`
(source 4776-4796, 4930-4937, 5684-5685, 5701-5704, 5918-5920)

Source of record: `the November 2 reference manuscript` (73 pages).

On the Floquet window `μ_n([-1,1]) ⊂ (0, 1/4)` (for large `n`, `mu_eventually_mem`), the pinned
operator `LjOp Pl K L μ : LStr →L[ℝ] AffSp K.as` satisfies `affIota K.as (LjOp Pl K L μ T) =
LjFun … μ … T`.  Combining `sourceLAmbientDiff` (`Continuity/Lj/AmbientDiff.lean`) with `sourceLN0`
(`SourceL/N0.lean`) exactly as in `sourceLBounded_of` (`SourceL.lean:409`) yields
`‖LjOp Pl K L μ - LjOp Pl K L μ₀‖ ≤ K |μ - μ₀|`, hence `ContinuousOn` on the window.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

/-- **`ljLipschitz`** (source 4776-4796, 4930-4937, 5701-5704): `μ`-Lipschitz `𝒜`-norm bound of
`LjFun`, from `sourceLAmbientDiff` and `sourceLN0` (cf. `sourceLBounded_of`, `SourceL.lean:409`). -/
theorem ljLipschitz (as mZ γ : ℝ) (χo χy : ℝ → ℝ) (has : 0 < as) (hmZ : 3 / 2 < mZ)
    (hγ : 0 < γ) :
    ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ (c ρb ν ε μ μ' : ℝ),
      LHyp c ν ε μ χo χy → LHyp c ν ε μ' χo χy →
      ∀ T : StrG c mZ ρb γ ν,
        affNorm as (LjFun c mZ ρb γ ν ε μ χo χy T - LjFun c mZ ρb γ ν ε μ' χo χy T) ≤
          C * ν⁻¹ ^ k * (ε ^ 3 * Real.exp (γ / ν)) * |μ - μ'| * ‖T‖ := by
  obtain ⟨C1, hC10, hC1⟩ := sourceLAmbientDiff as χo χy has
  obtain ⟨C2, k, hC2⟩ := sourceLN0 mZ γ hmZ hγ
  refine ⟨C1 * |C2|, k, by positivity, fun c ρb ν ε μ μ' h h' T => ?_⟩
  obtain ⟨hfin, hn⟩ := hC2 c ν ρb h.c_pos h.nu_pos h.nu_le T
  have hN0 := oldN0_nonneg c ν h.nu_pos (thinRep T)
  have he : 0 ≤ ε ^ 3 := pow_nonneg h.eps_pos.le 3
  have hn' : oldN0 c ν (thinRep T) ≤ |C2| * ν⁻¹ ^ k * Real.exp (γ / ν) * ‖T‖ := by
    refine hn.trans ?_
    have hfac : 0 ≤ ν⁻¹ ^ k * Real.exp (γ / ν) * ‖T‖ := by
      have := h.nu_pos; positivity
    calc C2 * ν⁻¹ ^ k * Real.exp (γ / ν) * ‖T‖
        = C2 * (ν⁻¹ ^ k * Real.exp (γ / ν) * ‖T‖) := by ring
      _ ≤ |C2| * (ν⁻¹ ^ k * Real.exp (γ / ν) * ‖T‖) :=
          mul_le_mul_of_nonneg_right (le_abs_self C2) hfac
      _ = |C2| * ν⁻¹ ^ k * Real.exp (γ / ν) * ‖T‖ := by ring
  have key : ∀ s, 0 < s →
      affTerm as 6 (LjFun c mZ ρb γ ν ε μ χo χy T - LjFun c mZ ρb γ ν ε μ' χo χy T) s ≤
        C1 * |C2| * ν⁻¹ ^ k * (ε ^ 3 * Real.exp (γ / ν)) * |μ - μ'| * ‖T‖ := by
    intro s hs
    have h1 := hC1 c ν ε μ μ' h h' (thinRep T) hfin s hs
    have h3 : C1 * ε ^ 3 * |μ - μ'| * oldN0 c ν (thinRep T) ≤
        C1 * ε ^ 3 * |μ - μ'| * (|C2| * ν⁻¹ ^ k * Real.exp (γ / ν) * ‖T‖) :=
      mul_le_mul_of_nonneg_left hn' (by positivity)
    unfold LjFun
    linarith
  unfold affNorm
  exact csSup_le ⟨_, ⟨1, Set.mem_Ioi.2 (one_pos : (0 : ℝ) < 1), rfl⟩⟩
    (by rintro _ ⟨s, hs, rfl⟩; exact key s hs)

/-- Operator-norm continuity of `μ ↦ LjOp Pl K L μ` on a subset `W ⊆ (0, 1/4)` where the `lj` pin
holds. -/
theorem ljOp_continuousOn (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel)
    (has : 0 < K.as) (hmZ : 3 / 2 < K.mZ) (hγ : 0 < gRate Pl) (hν1 : L.ν ≤ 1)
    (hχy : IsStreamCutoff K.χy) (W : Set ℝ) (hW : W ⊆ Ioo 0 (1 / 4))
    (hpin : ∀ μ ∈ W, ∃ Lj : LStr Pl K L →L[ℝ] AffSp K.as, ∀ T, affIota K.as (Lj T) =
      LjFun (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.χo K.χy T) :
    ContinuousOn (fun μ => LjOp Pl K L μ) W := by
  intro μ0 hμ0
  have hν : 0 < L.ν := L.ν_pos
  have hc : 0 < cOf L.ν := cOf_pos hν
  have hε : 0 < L.ε := L.ε_pos
  have hlhyp : ∀ μ ∈ W, LHyp (cOf L.ν) L.ν L.ε μ K.χo K.χy := fun μ hμ =>
    ⟨hc, hν, hν1, hε, (hW hμ).1, (hW hμ).2, K.hχo, hχy⟩
  obtain ⟨C, k, hC0, hLip⟩ := ljLipschitz K.as K.mZ (gRate Pl) K.χo K.χy has hmZ hγ
  set Lc : ℝ := C * L.ν⁻¹ ^ k * (L.ε ^ 3 * Real.exp (gRate Pl / L.ν)) with hLc
  have hLc0 : 0 ≤ Lc := by positivity
  have hbound : ∀ μ ∈ W, ‖LjOp Pl K L μ - LjOp Pl K L μ0‖ ≤ Lc * |μ - μ0| := by
    intro μ hμ
    refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hLc0 (abs_nonneg _)) fun T => ?_
    have hspec1 := Classical.epsilon_spec (hpin μ hμ) T
    have hspec0 := Classical.epsilon_spec (hpin μ0 hμ0) T
    rw [← affNorm_affIota K.as]
    have hsub : affIota K.as ((LjOp Pl K L μ - LjOp Pl K L μ0) T) =
        LjFun (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.χo K.χy T -
          LjFun (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ0 K.χo K.χy T := by
      unfold LjOp
      rw [sub_apply, map_sub, hspec1, hspec0]
    rw [hsub]
    exact hLip (cOf L.ν) (L.ρb Pl K) L.ν L.ε μ μ0 (hlhyp μ hμ) (hlhyp μ0 hμ0) T
  have hT : Tendsto (fun μ : ℝ => Lc * |μ - μ0|) (𝓝[W] μ0) (𝓝 0) := by
    have hcont : Continuous (fun μ : ℝ => Lc * |μ - μ0|) :=
      continuous_const.mul (continuous_id.sub continuous_const).abs
    have hz : Lc * |μ0 - μ0| = 0 := by simp
    rw [← hz]
    exact (hcont.tendsto μ0).mono_left nhdsWithin_le_nhds
  exact tendsto_iff_norm_sub_tendsto_zero.2
    (squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      (eventually_nhdsWithin_of_forall hbound) hT)

/-- **`LjCont`** on the concrete sequence (source 4776-4796, 5684-5685, 5701-5704, 5918-5920). -/
theorem SeqData.ljCont (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) : D.LjCont := by
  have hνlt : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n < 1 :=
    (retNu_tendsto D.σ₀ hst.omega_ne).eventually (Iio_mem_nhds zero_lt_one)
  filter_upwards [hst.pins, mu_eventually_mem D hst.omega_ne hst.sigma_pos hst.sigma_lt, hνlt]
    with n hp hn hlt
  refine ljOp_continuousOn D.Pl D.K (D.level n) hst.as_pos hst.mZ_gt hst.gamma_pos hlt.le
    hst.chiY (D.win n) ?_ ?_
  · rintro _ ⟨z, hz, rfl⟩
    have h := hn z hz
    constructor <;> linarith [h.1, h.2, hst.sigma_pos, hst.sigma_lt]
  · rintro _ ⟨z, hz, rfl⟩
    exact (hp z hz).lj

end UnforcedLeray.Short.PartIIIb.Concrete

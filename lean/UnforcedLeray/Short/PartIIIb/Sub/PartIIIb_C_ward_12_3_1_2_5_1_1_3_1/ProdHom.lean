import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1.FarOrg
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1.ProdHom.Point
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1.SliceBridge
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.GEQMem.Ddu

/-!
# `InletFnFarOfHom` (far product rule with homogeneous jets)

Source `the November 2 reference manuscript`
lines 2542-2549 (drift cancellation `L₀E = -νΔE` on the far set), 2563-2569 (slice bridge),
1206-1222 (homogeneous raw field). Given the homogeneous inlet jets `InletEFarHom`, the drift
identity `InletDriftFar` and the raw far jets `RawFarJets`, the far field `F = -∂_j(inletSrc)`
satisfies `InletFnFarDecay` with the `ϱ^{-3}(1+|y₃|/ϱ)^{-2}` envelope (`N = M + 2`).

Helpers: `ProdHom/Calc`, `ProdHom/AdvSplit`, `ProdHom/GradSplit`, `ProdHom/Bound`,
`ProdHom/Point`, `ProdHom/L0Far`.
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray.PhaseSpace
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Short.PartIIIb.Concrete.ProdHom in
theorem inletFnFarOfHom : InletFnFarOfHom := by
  intro h1 h2 h3
  intro lam q hq dm dp hdm
  obtain ⟨ν1, hν1, H1⟩ := h1 lam q hq dm dp hdm
  obtain ⟨ν2, hν2, H2⟩ := h2 lam q hq dm dp hdm
  obtain ⟨ν3, hν3, H3⟩ := h3 dm dp hdm
  refine ⟨min (min ν1 ν2) (min ν3 1), lt_min (lt_min hν1 hν2) (lt_min hν3 one_pos), ?_⟩
  intro p d hreg hν hmode z g hg
  have hν1' : p.ν ≤ ν1 := hν.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν2' : p.ν ≤ ν2 := hν.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν3' : p.ν ≤ ν3 := hν.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν1d : p.ν ≤ 1 := hν.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨CR, R0r, M, hR0r, hGU, hRb⟩ := H3 p d hreg hν3'
  have HE := H1 p d hreg hν1' hmode z g hg
  have HD := H2 p d hreg hν2' hmode z g hg
  intro i j
  obtain ⟨CE, R0E, hR0E, hEb⟩ := HE i (M + 2)
  obtain ⟨R0d, hR0d, hdr⟩ := HD i
  have hinlet := inlet_contDiff_joint lam q hq hreg hν1d hmode i
  have hE : ContDiff ℝ ∞ (p.Efun i) :=
    realCLI.toContinuousLinearMap.contDiff.comp hinlet
  obtain ⟨R0, hR0def⟩ : ∃ R0 : ℝ, R0 = max (max R0r R0E) R0d + 1 := ⟨_, rfl⟩
  have hA : R0r ≤ max (max R0r R0E) R0d := le_trans (le_max_left R0r R0E) (le_max_left _ R0d)
  have hB : R0E ≤ max (max R0r R0E) R0d := le_trans (le_max_right R0r R0E) (le_max_left _ R0d)
  have hC : R0d ≤ max (max R0r R0E) R0d := le_max_right _ R0d
  have hR0pos : 0 < R0 := by linarith
  have hR01 : 1 ≤ R0 := by linarith
  have hUo : IsOpen {x : ℝ × UnforcedLeray.Space | R0 < UnforcedLeray.Axi.ϱ x.2} := by
    apply isOpen_lt continuous_const
    unfold UnforcedLeray.Axi.ϱ
    fun_prop
  have hGU' : ContDiffOn ℝ ∞ (fun x : ℝ × UnforcedLeray.Space => p.raw x.1 x.2)
      {x : ℝ × UnforcedLeray.Space | R0 < UnforcedLeray.Axi.ϱ x.2} :=
    hGU.mono (fun x hx => by
      have hx' : R0 < UnforcedLeray.Axi.ϱ x.2 := hx
      show R0r < UnforcedLeray.Axi.ϱ x.2
      linarith)
  have hdrift : ∀ x ∈ {x : ℝ × UnforcedLeray.Space | R0 < UnforcedLeray.Axi.ϱ x.2},
      UnforcedLeray.PhaseSpace.dτ (p.Efun i) x -
        (1 / 2 : ℝ) • UnforcedLeray.PhaseSpace.radialT (p.Efun i) x -
        (1 / 2 : ℝ) • p.Efun i x = 0 := fun x hx => by
    have hx' : R0 < UnforcedLeray.Axi.ϱ x.2 := hx
    exact hdr x.1 x.2 (by linarith)
  have hCR0 : 0 ≤ max CR 0 := le_max_right _ _
  have hCE0 : 0 ≤ max CE 0 := le_max_right _ _
  refine ⟨|p.ν| * (3 * max CE 0) + 12 * (max CR 0 * max CE 0), R0, hR0pos, ?_⟩
  intro τ _ y hy
  have hy' : R0 < UnforcedLeray.Axi.ϱ y := hy
  have hz : (τ, y) ∈ {x : ℝ × UnforcedLeray.Space | R0 < UnforcedLeray.Axi.ϱ x.2} := hy'
  have hρ0 : 0 < UnforcedLeray.Axi.ϱ y := by linarith
  have hρ1 : 1 ≤ UnforcedLeray.Axi.ϱ y := by linarith
  have hsnn : 0 ≤ |y 2| / UnforcedLeray.Axi.ϱ y := div_nonneg (abs_nonneg (y 2)) hρ0.le
  have hs1 : 1 ≤ 1 + |y 2| / UnforcedLeray.Axi.ϱ y := by linarith
  have hsp : 0 < 1 + |y 2| / UnforcedLeray.Axi.ϱ y := by linarith
  have hRr : R0r < UnforcedLeray.Axi.ϱ y := by linarith
  have hRe : R0E < UnforcedLeray.Axi.ϱ y := by linarith
  have hR : ∀ k : ℕ, k ≤ 2 → ‖iteratedFDeriv ℝ k (fun w => (fun x : ℝ × UnforcedLeray.Space =>
      p.raw x.1 x.2) ((τ, y).1, w)) (τ, y).2‖ ≤
      max CR 0 * (UnforcedLeray.Axi.ϱ y ^ (-(1 + (k : ℝ))) *
        (1 + |y 2| / UnforcedLeray.Axi.ϱ y) ^ M) := by
    intro k hk
    have h := hRb τ y hRr k hk
    refine h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)
    exact mul_nonneg (Real.rpow_nonneg hρ0.le _) (pow_nonneg hsp.le M)
  have hEb' : ∀ k : ℕ, k ≤ 3 → ‖iteratedFDeriv ℝ k (fun w => p.Efun i ((τ, y).1, w)) (τ, y).2‖ ≤
      max CE 0 * (UnforcedLeray.Axi.ϱ y ^ (-(1 + (k : ℝ))) *
        (1 + |y 2| / UnforcedLeray.Axi.ϱ y) ^ (-((M + 2 : ℕ) : ℝ))) := by
    intro k hk
    have h := hEb τ y hRe k hk
    refine h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)
    exact mul_nonneg (Real.rpow_nonneg hρ0.le _) (Real.rpow_nonneg hsp.le _)
  have key := far_point p.ν j (p.Efun i) (fun x => p.raw x.1 x.2)
    {x : ℝ × UnforcedLeray.Space | R0 < UnforcedLeray.Axi.ϱ x.2} hUo hE hGU' hdrift (τ, y) hz M
    (max CR 0) (max CE 0) (UnforcedLeray.Axi.ϱ y) (1 + |y 2| / UnforcedLeray.Axi.ϱ y) hρ1 hs1
    hCR0 hCE0 hR hEb'
  unfold inletFn
  rw [Pi.neg_apply, norm_neg]
  exact key

end UnforcedLeray.Short.PartIIIb.Concrete

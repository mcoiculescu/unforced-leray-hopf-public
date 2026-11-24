import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2_2_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2_2_2.ProdHom2.Slice2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2_2_2.ProdHom2.RawFar3
import UnforcedLeray.Short.PartI.Tasks.TrainHeatFixed.TrainJetsBoundedFixed
import UnforcedLeray.Short.PartI.Tasks.TrainHeatFixed.TrainFluctAgeJetFixed

/-!
# `PartIII-b:C/ward/12/3/2/2/2/4`: `InletFn2FarOfHom` (order-2 far product rule)

Source `the November 2 reference manuscript`
lines 2542-2549 (drift cancellation `L₀E = -νΔE` on the far set), 2563-2569 (slice bridge),
1206-1222 (homogeneous raw field). Order-2 analogue of `inletFnFarOfHom` (`ProdHom.lean`).

On the open far set `U = {x | R₀ < ϱ(x.2)}` where the drift of `E_i = p.Efun i` vanishes
(`InletDriftFar`), `inletFn2 p i j l (τ, y) = ∂_j∂_l(-νΔE_i + (raw·∇)E_i + (E_i·∇)raw)`
(`inletFn2_far_slice_eq` in `ProdHom2/Slice2.lean`). Pairing `D^a raw` (`0 ≤ a ≤ 3`,
`O(ϱ^{-1-a} s^M)` from `RawFarJets3` in `ProdHom2/RawFar3.lean`, proved from the two Part I
fixed-parameter train bounds `PartI.TrainJetsBoundedFixed` and `PartI.TrainFluctAgeJetFixed`)
with `D^{3-a} E_i` (`O(ϱ^{-1-(3-a)} s^{-(M+2)})` from `InletEFarHom4` at `N = M + 2`), together
with `-ν ∂_j∂_l ΔE_i` (`O(ϱ^{-5} s^{-(M+2)})`), bounds every term by
`O(ϱ^{-5} s^{-2}) ≤ O(ϱ^{-3} s^{-2})` for `ϱ ≥ 1`.
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray.PhaseSpace
open scoped ContDiff
open UnforcedLeray.Cons.C03.Concrete (Params)

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace ProdHom2

/-- A product of two far-field bounds of total derivative order `3` (homogeneity `ϱ^{-5}`,
transverse weight `s^{-2}`), dominated by the `ϱ^{-3}s^{-2}` envelope for `ϱ ≥ 1`. -/
theorem prod3_bound (X Y c1 c2 ρ s : ℝ) (M a b : ℕ) (hab : a + b = 3) (hρ : 1 ≤ ρ) (hs : 1 ≤ s)
    (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) (hY0 : 0 ≤ Y)
    (hX : X ≤ c1 * (ρ ^ (-(1 + (a : ℝ))) * s ^ M))
    (hY : Y ≤ c2 * (ρ ^ (-(1 + (b : ℝ))) * s ^ (-((M + 2 : ℕ) : ℝ)))) :
    X * Y ≤ (c1 * c2) * (ρ ^ (-3 : ℝ) * s ^ (-2 : ℝ)) := by
  have hρ0 : 0 < ρ := by linarith
  have hs0 : 0 < s := by linarith
  have hab' : (a : ℝ) + (b : ℝ) = 3 := by exact_mod_cast hab
  have hAB : ρ ^ (-(1 + (a : ℝ))) * s ^ M * (ρ ^ (-(1 + (b : ℝ))) * s ^ (-((M + 2 : ℕ) : ℝ)))
      = ρ ^ (-5 : ℝ) * s ^ (-2 : ℝ) := by
    have h1 : ρ ^ (-(1 + (a : ℝ))) * ρ ^ (-(1 + (b : ℝ))) = ρ ^ (-5 : ℝ) := by
      rw [← Real.rpow_add hρ0]
      congr 1
      linarith
    have h2 : s ^ M * s ^ (-((M + 2 : ℕ) : ℝ)) = s ^ (-2 : ℝ) := by
      rw [← Real.rpow_natCast s M, ← Real.rpow_add hs0]
      congr 1
      push_cast
      ring
    calc ρ ^ (-(1 + (a : ℝ))) * s ^ M * (ρ ^ (-(1 + (b : ℝ))) * s ^ (-((M + 2 : ℕ) : ℝ)))
        = (ρ ^ (-(1 + (a : ℝ))) * ρ ^ (-(1 + (b : ℝ)))) *
            (s ^ M * s ^ (-((M + 2 : ℕ) : ℝ))) := by ring
      _ = ρ ^ (-5 : ℝ) * s ^ (-2 : ℝ) := by rw [h1, h2]
  have hA : 0 ≤ ρ ^ (-(1 + (a : ℝ))) * s ^ M := by positivity
  have hρ5 : ρ ^ (-5 : ℝ) ≤ ρ ^ (-3 : ℝ) := Real.rpow_le_rpow_of_exponent_le hρ (by norm_num)
  have hs2 : 0 ≤ s ^ (-2 : ℝ) := by positivity
  calc X * Y ≤ (c1 * (ρ ^ (-(1 + (a : ℝ))) * s ^ M)) *
        (c2 * (ρ ^ (-(1 + (b : ℝ))) * s ^ (-((M + 2 : ℕ) : ℝ)))) :=
          mul_le_mul hX hY hY0 (mul_nonneg hc1 hA)
    _ = (c1 * c2) * (ρ ^ (-(1 + (a : ℝ))) * s ^ M *
        (ρ ^ (-(1 + (b : ℝ))) * s ^ (-((M + 2 : ℕ) : ℝ)))) := by ring
    _ = (c1 * c2) * (ρ ^ (-5 : ℝ) * s ^ (-2 : ℝ)) := by rw [hAB]
    _ ≤ (c1 * c2) * (ρ ^ (-3 : ℝ) * s ^ (-2 : ℝ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hρ5 hs2) (mul_nonneg hc1 hc2)

/-- A single inlet factor of total order `4` (`ϱ^{-5}`, transverse weight `s^{-N}`, `N ≥ 2`),
dominated by the `ϱ^{-3}s^{-2}` envelope for `ϱ ≥ 1`. -/
theorem single4_bound (Y c ρ s : ℝ) (N : ℕ) (hN : 2 ≤ N) (hρ : 1 ≤ ρ) (hs : 1 ≤ s)
    (hc : 0 ≤ c)
    (hY : Y ≤ c * (ρ ^ (-(1 + ((4 : ℕ) : ℝ))) * s ^ (-((N : ℕ) : ℝ)))) :
    Y ≤ c * (ρ ^ (-3 : ℝ) * s ^ (-2 : ℝ)) := by
  have hρ0 : 0 < ρ := by linarith
  have hs0 : 0 < s := by linarith
  have hr : ρ ^ (-(1 + ((4 : ℕ) : ℝ))) = ρ ^ (-5 : ℝ) := by norm_num
  have hN' : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hsN : s ^ (-((N : ℕ) : ℝ)) ≤ s ^ (-2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hs (by linarith)
  have hρ5 : ρ ^ (-5 : ℝ) ≤ ρ ^ (-3 : ℝ) := Real.rpow_le_rpow_of_exponent_le hρ (by norm_num)
  have hρ5' : 0 ≤ ρ ^ (-5 : ℝ) := by positivity
  have hs2 : 0 ≤ s ^ (-2 : ℝ) := by positivity
  calc Y ≤ c * (ρ ^ (-(1 + ((4 : ℕ) : ℝ))) * s ^ (-((N : ℕ) : ℝ))) := hY
    _ = c * (ρ ^ (-5 : ℝ) * s ^ (-((N : ℕ) : ℝ))) := by rw [hr]
    _ ≤ c * (ρ ^ (-5 : ℝ) * s ^ (-2 : ℝ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsN hρ5') hc
    _ ≤ c * (ρ ^ (-3 : ℝ) * s ^ (-2 : ℝ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hρ5 hs2) hc

private lemma far_point2_algebra (ν : ℝ) (M : ℕ) (CR CE ρ s : ℝ)
    (hρ : 1 ≤ ρ) (hs : 1 ≤ s) (hCR : 0 ≤ CR) (hCE : 0 ≤ CE)
    (b a : ℕ → ℝ) (ha0 : ∀ k, 0 ≤ a k)
    (hR : ∀ k : ℕ, k ≤ 3 → b k ≤ CR * (ρ ^ (-(1 + (k : ℝ))) * s ^ M))
    (hEb : ∀ k : ℕ, k ≤ 4 → a k ≤ CE * (ρ ^ (-(1 + (k : ℝ))) * s ^ (-((M + 2 : ℕ) : ℝ)))) :
    |ν| * (3 * a 4) +
      3 * (b 0 * a 3 + b 1 * a 2 + (b 1 * a 2 + b 2 * a 1)) +
      3 * (a 0 * b 3 + a 1 * b 2 + (a 1 * b 2 + a 2 * b 1)) ≤
      (|ν| * (3 * CE) + 24 * (CR * CE)) * (ρ ^ (-3 : ℝ) * s ^ (-2 : ℝ)) := by
  set P : ℝ := ρ ^ (-3 : ℝ) * s ^ (-2 : ℝ)
  have h4 : a 4 ≤ CE * P :=
    single4_bound (a 4) CE ρ s (M + 2) (by omega) hρ hs hCE (hEb 4 (by omega))
  have h4' : |ν| * (3 * a 4) ≤ |ν| * (3 * (CE * P)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4 (by norm_num)) (abs_nonneg ν)
  have h03 := prod3_bound (b 0) (a 3) CR CE ρ s M 0 3 (by omega) hρ hs hCR hCE (ha0 3)
    (hR 0 (by omega)) (hEb 3 (by omega))
  have h12 := prod3_bound (b 1) (a 2) CR CE ρ s M 1 2 (by omega) hρ hs hCR hCE (ha0 2)
    (hR 1 (by omega)) (hEb 2 (by omega))
  have h21 := prod3_bound (b 2) (a 1) CR CE ρ s M 2 1 (by omega) hρ hs hCR hCE (ha0 1)
    (hR 2 (by omega)) (hEb 1 (by omega))
  have h30 := prod3_bound (b 3) (a 0) CR CE ρ s M 3 0 (by omega) hρ hs hCR hCE (ha0 0)
    (hR 3 (by omega)) (hEb 0 (by omega))
  have h30' : a 0 * b 3 ≤ (CR * CE) * P := by linarith
  have h21' : a 1 * b 2 ≤ (CR * CE) * P := by linarith
  have h12' : a 2 * b 1 ≤ (CR * CE) * P := by linarith
  calc |ν| * (3 * a 4) +
        3 * (b 0 * a 3 + b 1 * a 2 + (b 1 * a 2 + b 2 * a 1)) +
        3 * (a 0 * b 3 + a 1 * b 2 + (a 1 * b 2 + a 2 * b 1))
      ≤ |ν| * (3 * (CE * P)) +
        3 * ((CR * CE) * P + (CR * CE) * P + ((CR * CE) * P + (CR * CE) * P)) +
        3 * ((CR * CE) * P + (CR * CE) * P + ((CR * CE) * P + (CR * CE) * P)) := by linarith
    _ = (|ν| * (3 * CE) + 24 * (CR * CE)) * P := by ring

open Jets2 in
/-- **Far pointwise bound for `inletFn2 p i j l (τ, y)`** (order-2 analogue of `ProdHom.far_point`,
`ProdHom/Point.lean:82`). Assumes the far-field raw bounds (`hR`, `k ≤ 3`) and inlet bounds
(`hEb`, `k ≤ 4`) at the slice `(τ, y)`, drift cancellation on the open set `U`, and `ρ, s ≥ 1`. -/
theorem far_point2 (p : Params) (i : Fin 2) (j l : Fin 3)
    (U : Set (ℝ × UnforcedLeray.Space)) (hU : IsOpen U) (hE : ContDiff ℝ ∞ (p.Efun i))
    (hGU : ContDiffOn ℝ ∞ (fun x : ℝ × UnforcedLeray.Space => p.raw x.1 x.2) U)
    (hdrift : ∀ x ∈ U, dτ (p.Efun i) x - (1 / 2 : ℝ) • radialT (p.Efun i) x -
      (1 / 2 : ℝ) • p.Efun i x = 0)
    (τ : ℝ) (y : UnforcedLeray.Space) (hz : (τ, y) ∈ U) (M : ℕ) (CR CE ρ s : ℝ)
    (hρ : 1 ≤ ρ) (hs : 1 ≤ s) (hCR : 0 ≤ CR) (hCE : 0 ≤ CE)
    (hR : ∀ k : ℕ, k ≤ 3 → ‖iteratedFDeriv ℝ k (p.raw τ) y‖ ≤
      CR * (ρ ^ (-(1 + (k : ℝ))) * s ^ M))
    (hEb : ∀ k : ℕ, k ≤ 4 → ‖iteratedFDeriv ℝ k (fun w => p.Efun i (τ, w)) y‖ ≤
      CE * (ρ ^ (-(1 + (k : ℝ))) * s ^ (-((M + 2 : ℕ) : ℝ)))) :
    ‖inletFn2 p i j l (τ, y)‖ ≤
      (|p.ν| * (3 * CE) + 24 * (CR * CE)) * (ρ ^ (-3 : ℝ) * s ^ (-2 : ℝ)) := by
  set Uy : Set UnforcedLeray.Space := {x | (τ, x) ∈ U}
  have hUy : IsOpen Uy := hU.preimage (continuous_const.prodMk continuous_id)
  have hyU : y ∈ Uy := hz
  have hsl : ContDiff ℝ ∞ (fun x : UnforcedLeray.Space => ((τ, x) : ℝ × UnforcedLeray.Space)) :=
    contDiff_const.prodMk contDiff_id
  have he : ContDiff ℝ ∞ (fun w : UnforcedLeray.Space => p.Efun i (τ, w)) := hE.comp hsl
  have hr : ContDiffOn ℝ ∞ (p.raw τ) Uy :=
    (hGU.comp hsl.contDiffOn (fun x hx => hx)).congr (fun _ _ => rfl)
  rw [inletFn2_far_slice_eq p i j l hU hE hGU hdrift τ y hz]
  refine (norm_D2_Sfar_le hUy he hr p.ν hyU j l).trans ?_
  exact far_point2_algebra p.ν M CR CE ρ s hρ hs hCR hCE
    (fun k => ‖iteratedFDeriv ℝ k (p.raw τ) y‖)
    (fun k => ‖iteratedFDeriv ℝ k (fun w => p.Efun i (τ, w)) y‖)
    (fun k => norm_nonneg _) hR hEb

end ProdHom2

open ProdHom2 in
/-- **`InletFn2FarOfHom` from `RawFarJets3`** (order-2 analogue of `inletFnFarOfHom`,
`ProdHom.lean:30`). -/
theorem inletFn2FarOfHom_of (h3 : RawFarJets3) : InletFn2FarOfHom := by
  intro h1 h2 lam q hq dm dp hdm
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
  intro i j l
  obtain ⟨CE, R0E, hR0E, hEb⟩ := HE i (M + 2)
  obtain ⟨R0d, hR0d, hdr⟩ := HD i
  have hinlet := inlet_contDiff_joint lam q hq hreg hν1d hmode i
  have hE : ContDiff ℝ ∞ (p.Efun i) := contDiff_realC_meas.comp hinlet
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
  refine ⟨|p.ν| * (3 * max CE 0) + 24 * (max CR 0 * max CE 0), R0, hR0pos, ?_⟩
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
  have hR : ∀ k : ℕ, k ≤ 3 → ‖iteratedFDeriv ℝ k (p.raw τ) y‖ ≤
      max CR 0 * (UnforcedLeray.Axi.ϱ y ^ (-(1 + (k : ℝ))) *
        (1 + |y 2| / UnforcedLeray.Axi.ϱ y) ^ M) := by
    intro k hk
    have h := hRb τ y hRr k hk
    refine h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)
    exact mul_nonneg (Real.rpow_nonneg hρ0.le _) (pow_nonneg hsp.le M)
  have hEb' : ∀ k : ℕ, k ≤ 4 → ‖iteratedFDeriv ℝ k (fun w => p.Efun i (τ, w)) y‖ ≤
      max CE 0 * (UnforcedLeray.Axi.ϱ y ^ (-(1 + (k : ℝ))) *
        (1 + |y 2| / UnforcedLeray.Axi.ϱ y) ^ (-((M + 2 : ℕ) : ℝ))) := by
    intro k hk
    have h := hEb τ y hRe k hk
    refine h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)
    exact mul_nonneg (Real.rpow_nonneg hρ0.le _) (Real.rpow_nonneg hsp.le _)
  exact far_point2 p i j l
    {x : ℝ × UnforcedLeray.Space | R0 < UnforcedLeray.Axi.ϱ x.2} hUo hE hGU' hdrift τ y hz M
    (max CR 0) (max CE 0) (UnforcedLeray.Axi.ϱ y) (1 + |y 2| / UnforcedLeray.Axi.ϱ y) hρ1 hs1
    hCR0 hCE0 hR hEb'

/-- `InletFn2FarOfHom` from the two pending Part I fixed-parameter train bounds
`PartI.TrainJetsBoundedFixed` (`PartI:HF/1`) and `PartI.TrainFluctAgeJetFixed` (`PartI:HF/2`). -/
theorem inletFn2FarOfHom_of_partI (h1 : UnforcedLeray.Short.PartI.TrainJetsBoundedFixed)
    (h2 : UnforcedLeray.Short.PartI.TrainFluctAgeJetFixed) : InletFn2FarOfHom :=
  inletFn2FarOfHom_of (rawFarJets3_of h1 h2)

theorem inletFn2FarOfHom : InletFn2FarOfHom :=
  inletFn2FarOfHom_of_partI
    UnforcedLeray.Short.PartI.trainJetsBoundedFixed
    UnforcedLeray.Short.PartI.trainFluctAgeJetFixed

end UnforcedLeray.Short.PartIIIb.Concrete

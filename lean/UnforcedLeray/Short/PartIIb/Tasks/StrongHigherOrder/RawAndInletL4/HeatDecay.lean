import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.Sub.RingLiftOffAxis_Sub.HeatFieldJet
import UnforcedLeray.Lib.HeatR3.Anisotropic
import UnforcedLeray.Lib.HeatR3.Weighted

/-!
# Axial decay of the heat-term fields (helper for `PartII-b:S2/3`)

Source of record: `the November 2 reference manuscript`, lines 2548-2550 ("On
`ϱ<R`, take the all-age heat expansion to a sufficiently high finite order: its even radial powers
extend smoothly through the axis and its weighted remainder gives arbitrary axial decay"),
1310-1313 (the heat terms are polynomials in `w = ϱ²` times Gaussian derivatives in `y₃`).

`heatField ν R j` is a finite sum of products of polynomials in `y₀, y₁` (bounded jets on
`ϱ² ≤ W`, `HeatJetBdd`) and one Gaussian derivative `g_ν^{(n)}(y₃)`, whose jets satisfy
`(1+|z|)|D^k g_ν^{(n)}(z)| ≤ C` (`abs_pow_mul_iteratedDeriv_lineGauss_le`).  The predicate
`HeatJetDec W f`: `(1+|y₃|)‖D^k f(y)‖ ≤ C` on `ϱ² ≤ W`, is closed under sums, constant multiples
and products with a `HeatJetBdd` factor (Leibniz), so `heatSum ν R a N` satisfies it.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb.RawAndInletL4

open UnforcedLeray UnforcedLeray.Short.PartIIIb.Concrete

/-- Axially weighted bounded Cartesian jets of `f` on the region `ϱ² ≤ W`. -/
abbrev HeatJetDec (W : ℝ) {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Space → F) : Prop :=
  ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Space, Axi.ϱ y ^ 2 ≤ W →
    (1 + |y 2|) * ‖iteratedFDeriv ℝ k f y‖ ≤ C

theorem hjdAdd {W : ℝ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : Space → F} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (Hf : HeatJetDec W f) (Hg : HeatJetDec W g) : HeatJetDec W (fun y => f y + g y) := by
  intro k
  obtain ⟨Cf, hCf0, hCf⟩ := Hf k
  obtain ⟨Cg, hCg0, hCg⟩ := Hg k
  refine ⟨Cf + Cg, add_nonneg hCf0 hCg0, fun y hy => ?_⟩
  have hfa : ContDiffAt ℝ k f y := hf.contDiffAt.of_le (by exact_mod_cast le_top)
  have hga : ContDiffAt ℝ k g y := hg.contDiffAt.of_le (by exact_mod_cast le_top)
  have e : iteratedFDeriv ℝ k (fun y => f y + g y) y =
      iteratedFDeriv ℝ k f y + iteratedFDeriv ℝ k g y := iteratedFDeriv_add_apply hfa hga
  rw [e]
  have hw : 0 ≤ 1 + |y 2| := by positivity
  calc (1 + |y 2|) * ‖iteratedFDeriv ℝ k f y + iteratedFDeriv ℝ k g y‖
      ≤ (1 + |y 2|) * (‖iteratedFDeriv ℝ k f y‖ + ‖iteratedFDeriv ℝ k g y‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) hw
    _ = (1 + |y 2|) * ‖iteratedFDeriv ℝ k f y‖ + (1 + |y 2|) * ‖iteratedFDeriv ℝ k g y‖ := by
        ring
    _ ≤ Cf + Cg := add_le_add (hCf y hy) (hCg y hy)

theorem hjdSmulConst {W : ℝ} {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) (v : Space)
    (Hf : HeatJetDec W f) : HeatJetDec W (fun y => f y • v) := by
  intro k
  obtain ⟨Cf, hCf0, hCf⟩ := Hf k
  set L : ℝ →L[ℝ] Space := (ContinuousLinearMap.id ℝ ℝ).smulRight v with hLdef
  have hfun : (fun y => f y • v) = L ∘ f := by
    funext y
    simp [hLdef]
  refine ⟨‖L‖ * Cf, mul_nonneg (norm_nonneg _) hCf0, fun y hy => ?_⟩
  have hfa : ContDiffAt ℝ ∞ f y := hf.contDiffAt
  rw [hfun]
  have hw : 0 ≤ 1 + |y 2| := by positivity
  have h1 := L.norm_iteratedFDeriv_comp_left hfa (n := k) (by exact_mod_cast le_top)
  calc (1 + |y 2|) * ‖iteratedFDeriv ℝ k (L ∘ f) y‖
      ≤ (1 + |y 2|) * (‖L‖ * ‖iteratedFDeriv ℝ k f y‖) := mul_le_mul_of_nonneg_left h1 hw
    _ = ‖L‖ * ((1 + |y 2|) * ‖iteratedFDeriv ℝ k f y‖) := by ring
    _ ≤ ‖L‖ * Cf := mul_le_mul_of_nonneg_left (hCf y hy) (norm_nonneg _)

/-- Leibniz: a bounded-jet factor times an axially decaying factor. -/
theorem hjdMulL {W : ℝ} {f g : Space → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (Hf : HeatJetBdd W f) (Hg : HeatJetDec W g) : HeatJetDec W (fun y => f y * g y) := by
  intro k
  choose Cf hCf0 hCf using Hf
  choose Cg hCg0 hCg using Hg
  refine ⟨∑ i ∈ Finset.range (k + 1), ((k.choose i : ℝ) * Cf i) * Cg (k - i),
    Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hCf0 i)) (hCg0 _),
    fun y hy => ?_⟩
  have hw : 0 ≤ 1 + |y 2| := by positivity
  refine (mul_le_mul_of_nonneg_left
    (norm_iteratedFDeriv_mul_le hf hg y (by exact_mod_cast le_top)) hw).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  calc (1 + |y 2|) * ((k.choose i : ℝ) * ‖iteratedFDeriv ℝ i f y‖ *
        ‖iteratedFDeriv ℝ (k - i) g y‖)
      = ((k.choose i : ℝ) * ‖iteratedFDeriv ℝ i f y‖) *
          ((1 + |y 2|) * ‖iteratedFDeriv ℝ (k - i) g y‖) := by ring
    _ ≤ ((k.choose i : ℝ) * Cf i) * Cg (k - i) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hCf i y hy) (Nat.cast_nonneg _)) (hCg _ y hy)
        (by positivity) (mul_nonneg (Nat.cast_nonneg _) (hCf0 i))

/-- Leibniz: an axially decaying factor times a bounded-jet factor. -/
theorem hjdMulR {W : ℝ} {f g : Space → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (Hf : HeatJetDec W f) (Hg : HeatJetBdd W g) : HeatJetDec W (fun y => f y * g y) := by
  intro k
  choose Cf hCf0 hCf using Hf
  choose Cg hCg0 hCg using Hg
  refine ⟨∑ i ∈ Finset.range (k + 1), ((k.choose i : ℝ) * Cf i) * Cg (k - i),
    Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hCf0 i)) (hCg0 _),
    fun y hy => ?_⟩
  have hw : 0 ≤ 1 + |y 2| := by positivity
  refine (mul_le_mul_of_nonneg_left
    (norm_iteratedFDeriv_mul_le hf hg y (by exact_mod_cast le_top)) hw).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  calc (1 + |y 2|) * ((k.choose i : ℝ) * ‖iteratedFDeriv ℝ i f y‖ *
        ‖iteratedFDeriv ℝ (k - i) g y‖)
      = ((k.choose i : ℝ) * ((1 + |y 2|) * ‖iteratedFDeriv ℝ i f y‖)) *
          ‖iteratedFDeriv ℝ (k - i) g y‖ := by ring
    _ ≤ ((k.choose i : ℝ) * Cf i) * Cg (k - i) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hCf i y hy) (Nat.cast_nonneg _)) (hCg _ y hy)
        (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hCf0 i))

/-- A function of `y₃` alone whose jets decay like `(1+|z|)⁻¹`. -/
theorem hjdCompProj2 {W : ℝ} {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (Hg : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ, (1 + |z|) * ‖iteratedFDeriv ℝ k g z‖ ≤ C) :
    HeatJetDec W (fun y : Space => g (y 2)) := by
  intro k
  obtain ⟨Cg, hCg0, hCg⟩ := Hg k
  set P : Space →L[ℝ] ℝ := EuclideanSpace.proj (2 : Fin 3) with hP
  have hfun : (fun y : Space => g (y 2)) = g ∘ P := by
    funext y
    rfl
  refine ⟨Cg * ‖P‖ ^ k, mul_nonneg hCg0 (pow_nonneg (norm_nonneg _) _), fun y _ => ?_⟩
  rw [hfun, ContinuousLinearMap.iteratedFDeriv_comp_right P hg y (by exact_mod_cast le_top)]
  have h1 := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ k g (P y)) (fun _ : Fin k => P)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
  have hPy : P y = y 2 := rfl
  have hw : 0 ≤ 1 + |y 2| := by positivity
  calc (1 + |y 2|) * ‖(iteratedFDeriv ℝ k g (P y)).compContinuousLinearMap fun _ => P‖
      ≤ (1 + |y 2|) * (‖iteratedFDeriv ℝ k g (P y)‖ * ‖P‖ ^ k) :=
        mul_le_mul_of_nonneg_left h1 hw
    _ = ((1 + |y 2|) * ‖iteratedFDeriv ℝ k g (y 2)‖) * ‖P‖ ^ k := by rw [hPy]; ring
    _ ≤ Cg * ‖P‖ ^ k := mul_le_mul_of_nonneg_right (hCg (y 2)) (pow_nonneg (norm_nonneg _) _)

/-- Weighted Gaussian jets: `(1+|z|)‖D^k g_ν^{(m)}(z)‖ ≤ C`. -/
theorem profileDeriv_wtd {ν : ℝ} (hν : 0 < ν) (m k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ,
      (1 + |z|) * ‖iteratedFDeriv ℝ k (UnforcedLeray.B0191.profileDeriv ν m) z‖ ≤ C := by
  obtain ⟨C0, hC0, h0⟩ := hfjProfileDeriv hν m k
  obtain ⟨C1, hC1, h1⟩ := UnforcedLeray.Heat.abs_pow_mul_iteratedDeriv_lineGauss_le 1 (m + k)
  have hfun : UnforcedLeray.B0191.profile ν = UnforcedLeray.Heat.lineGauss ν := by
    funext x
    simp only [UnforcedLeray.B0191.profile, UnforcedLeray.B0191.heatKernel,
      UnforcedLeray.Heat.lineGauss, mul_one]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le)
      hν.le)]
    ring_nf
  set G : ℝ := (4 * Real.pi * (4 * ν)) ^ (-((1 : ℕ) : ℝ) / 2) with hG
  have hG0 : 0 ≤ G := by positivity
  set D : ℝ := C1 * ν ^ ((((1 : ℕ) : ℝ) - ((m + k : ℕ) : ℝ)) / 2) with hD
  have hD0 : 0 ≤ D := by positivity
  refine ⟨C0 + D * G, by positivity, fun z => ?_⟩
  have e : ‖iteratedFDeriv ℝ k (UnforcedLeray.B0191.profileDeriv ν m) z‖ =
      ‖iteratedDeriv (m + k) (UnforcedLeray.Heat.lineGauss ν) z‖ := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hfjProfileDerivEq ν k m]
    unfold UnforcedLeray.B0191.profileDeriv
    rw [hfun]
  have hz := h1 hν z
  rw [pow_one] at hz
  have hg4 : UnforcedLeray.Heat.lineGauss (4 * ν) z ≤ G :=
    UnforcedLeray.Heat.lineGauss_le (by positivity) z
  have hz' : |z| * ‖iteratedFDeriv ℝ k (UnforcedLeray.B0191.profileDeriv ν m) z‖ ≤ D * G := by
    rw [e]
    refine hz.trans ?_
    exact mul_le_mul_of_nonneg_left hg4 hD0
  have h0z := h0 z
  nlinarith

theorem hjdProfileDeriv {W : ℝ} {ν : ℝ} (hν : 0 < ν) (m : ℕ) :
    HeatJetDec W (fun y : Space => UnforcedLeray.B0191.profileDeriv ν m (y 2)) :=
  hjdCompProj2 (UnforcedLeray.Short.IIb.contDiff_profileDeriv ν m)
    (fun k => profileDeriv_wtd hν m k)

/-- **Axial decay of every heat-term field** on `ϱ² ≤ W`. -/
theorem heatFieldDec {ν : ℝ} (hν : 0 < ν) (R : ℝ) (j : ℕ) (W : ℝ) :
    HeatJetDec W (heatField ν R j) := by
  have c0 : ContDiff ℝ ∞ (fun y : Space => y 0) := by fun_prop
  have c1 : ContDiff ℝ ∞ (fun y : Space => y 1) := by fun_prop
  have c2 : ContDiff ℝ ∞ (fun y : Space => y 2) := by fun_prop
  have cw : ContDiff ℝ ∞ (fun y : Space => y 0 ^ 2 + y 1 ^ 2) := by fun_prop
  have cwj : ContDiff ℝ ∞ (fun y : Space => (y 0 ^ 2 + y 1 ^ 2) ^ j) := cw.pow j
  have cg : ∀ n : ℕ, ContDiff ℝ ∞ (fun y : Space => UnforcedLeray.B0191.profileDeriv ν n (y 2)) :=
    fun n => (UnforcedLeray.Short.IIb.contDiff_profileDeriv ν n).comp c2
  have h0 : HeatJetBdd W (fun y : Space => y 0) :=
    hfjCoord (W := W) 0 (fun y => le_add_of_nonneg_right (sq_nonneg _))
  have h1 : HeatJetBdd W (fun y : Space => y 1) :=
    hfjCoord (W := W) 1 (fun y => le_add_of_nonneg_left (sq_nonneg _))
  have hw : HeatJetBdd W (fun y : Space => y 0 ^ 2 + y 1 ^ 2) :=
    hfjAdd (f := fun y : Space => y 0 ^ 2) (g := fun y : Space => y 1 ^ 2)
      (by fun_prop) (by fun_prop) (hfjPow c0 h0 2) (hfjPow c1 h1 2)
  have hP : HeatJetBdd W (fun y : Space => (y 0 ^ 2 + y 1 ^ 2) ^ j) := hfjPow cw hw j
  have hA : HeatJetDec W (hfjA ν R j) := by
    unfold hfjA
    exact hjdMulL (f := fun _ : Space => -((R ^ (2 * j + 1))⁻¹))
      (g := fun y : Space => (y 0 ^ 2 + y 1 ^ 2) ^ j *
        UnforcedLeray.B0191.profileDeriv ν (2 * j + 1) (y 2))
      contDiff_const (cwj.mul (cg (2 * j + 1))) (hfjConst _)
      (hjdMulL cwj (cg (2 * j + 1)) hP (hjdProfileDeriv hν (2 * j + 1)))
  have hB : HeatJetDec W (hfjB ν R j) := by
    unfold hfjB
    exact hjdMulL (f := fun _ : Space => (2 * (j : ℝ) + 2) * (R ^ (2 * j + 1))⁻¹)
      (g := fun y : Space => (y 0 ^ 2 + y 1 ^ 2) ^ j *
        UnforcedLeray.B0191.profileDeriv ν (2 * j) (y 2))
      contDiff_const (cwj.mul (cg (2 * j))) (hfjConst _)
      (hjdMulL cwj (cg (2 * j)) hP (hjdProfileDeriv hν (2 * j)))
  have cA : ContDiff ℝ ∞ (hfjA ν R j) := by
    unfold hfjA
    exact contDiff_const.mul (cwj.mul (cg (2 * j + 1)))
  have cB : ContDiff ℝ ∞ (hfjB ν R j) := by
    unfold hfjB
    exact contDiff_const.mul (cwj.mul (cg (2 * j)))
  have hT0 : HeatJetDec W (fun y : Space => (hfjA ν R j y * y 0) • coordinateVector 0) :=
    hjdSmulConst (cA.mul c0) (coordinateVector 0) (hjdMulR cA c0 hA h0)
  have hT1 : HeatJetDec W (fun y : Space => (hfjA ν R j y * y 1) • coordinateVector 1) :=
    hjdSmulConst (cA.mul c1) (coordinateVector 1) (hjdMulR cA c1 hA h1)
  have hT2 : HeatJetDec W (fun y : Space => hfjB ν R j y • Axi.e3) :=
    hjdSmulConst cB Axi.e3 hB
  have cT0 : ContDiff ℝ ∞ (fun y : Space => (hfjA ν R j y * y 0) • coordinateVector 0) :=
    (cA.mul c0).smul contDiff_const
  have cT1 : ContDiff ℝ ∞ (fun y : Space => (hfjA ν R j y * y 1) • coordinateVector 1) :=
    (cA.mul c1).smul contDiff_const
  have cT2 : ContDiff ℝ ∞ (fun y : Space => hfjB ν R j y • Axi.e3) :=
    cB.smul contDiff_const
  have hall : HeatJetDec W (fun y : Space => (hfjA ν R j y * y 0) • coordinateVector 0 +
      ((hfjA ν R j y * y 1) • coordinateVector 1 + hfjB ν R j y • Axi.e3)) :=
    hjdAdd cT0 (cT1.add cT2) hT0 (hjdAdd cT1 cT2 hT1 hT2)
  have hfun : heatField ν R j = fun y : Space => (hfjA ν R j y * y 0) • coordinateVector 0 +
      ((hfjA ν R j y * y 1) • coordinateVector 1 + hfjB ν R j y • Axi.e3) :=
    funext (hfjField ν R j)
  rw [hfun]
  exact hall

/-- **Axial decay of the heat sum** on `ϱ² ≤ W`: `(1+|y₃|)‖D^k heatSum(y)‖ ≤ C`. -/
theorem heatSumDec {ν : ℝ} (hν : 0 < ν) (R : ℝ) (a : ℕ → ℝ) (N : ℕ) (W : ℝ) :
    HeatJetDec W (heatSum ν R a N) := by
  intro k
  choose CH hCH0 hCH using fun j => heatFieldDec hν R j W k
  refine ⟨∑ j ∈ Finset.range (N + 1), |a j| * CH j,
    Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (hCH0 j), fun y hy => ?_⟩
  have hsm : ∀ j ∈ Finset.range (N + 1), ContDiff ℝ k (fun y => a j • heatField ν R j y) :=
    fun j _ => ((contDiff_heatField ν R j).const_smul (a j)).of_le (m := (k : WithTop ℕ∞))
      (by exact_mod_cast le_top)
  have e : iteratedFDeriv ℝ k (heatSum ν R a N) y =
      ∑ j ∈ Finset.range (N + 1), iteratedFDeriv ℝ k (fun y => a j • heatField ν R j y) y := by
    have h := iteratedFDeriv_sum (𝕜 := ℝ) (i := k) hsm
    have h' := congrFun h y
    rw [Finset.sum_apply] at h'
    exact h'
  rw [e]
  have hw : 0 ≤ 1 + |y 2| := by positivity
  refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) hw).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [iteratedFDeriv_const_smul_apply'
      (((contDiff_heatField ν R j).contDiffAt (x := y)).of_le (m := (k : WithTop ℕ∞))
        (by exact_mod_cast le_top)),
    norm_smul, Real.norm_eq_abs]
  calc (1 + |y 2|) * (|a j| * ‖iteratedFDeriv ℝ k (heatField ν R j) y‖)
      = |a j| * ((1 + |y 2|) * ‖iteratedFDeriv ℝ k (heatField ν R j) y‖) := by ring
    _ ≤ |a j| * CH j := mul_le_mul_of_nonneg_left (hCH j y hy) (abs_nonneg _)

end UnforcedLeray.Short.IIb.RawAndInletL4

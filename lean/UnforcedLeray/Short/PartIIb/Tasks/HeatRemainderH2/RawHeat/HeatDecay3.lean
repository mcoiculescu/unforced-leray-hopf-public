import UnforcedLeray.Short.PartIIb.Tasks.StrongHigherOrder.RawAndInletL4
import UnforcedLeray.Short.PartIIb.Tasks.StrongHigherOrder.RawAndInletL4.HeatDecay

/-!
# Cubic axial decay of `heatSum` and near-axis raw decay (helper for `PartII-b:B3/2/1/1`)

Source of record: `the November 2 reference manuscript`, lines 2548-2550,
2593-2597 (`short-bg:raw-heat`: on bounded radii, the all-age heat expansion gives arbitrary axial
decay `(1 + |y₃|)^{-3}` of `p.raw τ`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb.RawHeatAux

open UnforcedLeray UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Short.IIb.RawAndInletL4

/-- Cubic axially weighted bounded Cartesian jets of `f` on `ϱ² ≤ W`. -/
abbrev HeatJetDec3 (W : ℝ) {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Space → F) : Prop :=
  ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Space, Axi.ϱ y ^ 2 ≤ W →
    (1 + |y 2|) ^ 3 * ‖iteratedFDeriv ℝ k f y‖ ≤ C

theorem hjd3Add {W : ℝ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : Space → F} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (Hf : HeatJetDec3 W f) (Hg : HeatJetDec3 W g) : HeatJetDec3 W (fun y => f y + g y) := by
  intro k
  obtain ⟨Cf, hCf0, hCf⟩ := Hf k
  obtain ⟨Cg, hCg0, hCg⟩ := Hg k
  refine ⟨Cf + Cg, add_nonneg hCf0 hCg0, fun y hy => ?_⟩
  have hfa : ContDiffAt ℝ k f y := hf.contDiffAt.of_le (by exact_mod_cast le_top)
  have hga : ContDiffAt ℝ k g y := hg.contDiffAt.of_le (by exact_mod_cast le_top)
  have e : iteratedFDeriv ℝ k (fun y => f y + g y) y =
      iteratedFDeriv ℝ k f y + iteratedFDeriv ℝ k g y := iteratedFDeriv_add_apply hfa hga
  rw [e]
  have hw : 0 ≤ (1 + |y 2|) ^ 3 := by positivity
  calc (1 + |y 2|) ^ 3 * ‖iteratedFDeriv ℝ k f y + iteratedFDeriv ℝ k g y‖
      ≤ (1 + |y 2|) ^ 3 * (‖iteratedFDeriv ℝ k f y‖ + ‖iteratedFDeriv ℝ k g y‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) hw
    _ = (1 + |y 2|) ^ 3 * ‖iteratedFDeriv ℝ k f y‖ +
          (1 + |y 2|) ^ 3 * ‖iteratedFDeriv ℝ k g y‖ := by ring
    _ ≤ Cf + Cg := add_le_add (hCf y hy) (hCg y hy)

theorem hjd3SmulConst {W : ℝ} {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) (v : Space)
    (Hf : HeatJetDec3 W f) : HeatJetDec3 W (fun y => f y • v) := by
  intro k
  obtain ⟨Cf, hCf0, hCf⟩ := Hf k
  set L : ℝ →L[ℝ] Space := (ContinuousLinearMap.id ℝ ℝ).smulRight v with hLdef
  have hfun : (fun y => f y • v) = L ∘ f := by
    funext y
    simp [hLdef]
  refine ⟨‖L‖ * Cf, mul_nonneg (norm_nonneg _) hCf0, fun y hy => ?_⟩
  have hfa : ContDiffAt ℝ ∞ f y := hf.contDiffAt
  rw [hfun]
  have hw : 0 ≤ (1 + |y 2|) ^ 3 := by positivity
  have h1 := L.norm_iteratedFDeriv_comp_left hfa (n := k) (by exact_mod_cast le_top)
  calc (1 + |y 2|) ^ 3 * ‖iteratedFDeriv ℝ k (L ∘ f) y‖
      ≤ (1 + |y 2|) ^ 3 * (‖L‖ * ‖iteratedFDeriv ℝ k f y‖) := mul_le_mul_of_nonneg_left h1 hw
    _ = ‖L‖ * ((1 + |y 2|) ^ 3 * ‖iteratedFDeriv ℝ k f y‖) := by ring
    _ ≤ ‖L‖ * Cf := mul_le_mul_of_nonneg_left (hCf y hy) (norm_nonneg _)

theorem hjd3MulL {W : ℝ} {f g : Space → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (Hf : HeatJetBdd W f) (Hg : HeatJetDec3 W g) : HeatJetDec3 W (fun y => f y * g y) := by
  intro k
  choose Cf hCf0 hCf using Hf
  choose Cg hCg0 hCg using Hg
  refine ⟨∑ i ∈ Finset.range (k + 1), ((k.choose i : ℝ) * Cf i) * Cg (k - i),
    Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hCf0 i)) (hCg0 _),
    fun y hy => ?_⟩
  have hw : 0 ≤ (1 + |y 2|) ^ 3 := by positivity
  refine (mul_le_mul_of_nonneg_left
    (norm_iteratedFDeriv_mul_le hf hg y (by exact_mod_cast le_top)) hw).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  calc (1 + |y 2|) ^ 3 * ((k.choose i : ℝ) * ‖iteratedFDeriv ℝ i f y‖ *
        ‖iteratedFDeriv ℝ (k - i) g y‖)
      = ((k.choose i : ℝ) * ‖iteratedFDeriv ℝ i f y‖) *
          ((1 + |y 2|) ^ 3 * ‖iteratedFDeriv ℝ (k - i) g y‖) := by ring
    _ ≤ ((k.choose i : ℝ) * Cf i) * Cg (k - i) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hCf i y hy) (Nat.cast_nonneg _)) (hCg _ y hy)
        (by positivity) (mul_nonneg (Nat.cast_nonneg _) (hCf0 i))

theorem hjd3MulR {W : ℝ} {f g : Space → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (Hf : HeatJetDec3 W f) (Hg : HeatJetBdd W g) : HeatJetDec3 W (fun y => f y * g y) := by
  intro k
  choose Cf hCf0 hCf using Hf
  choose Cg hCg0 hCg using Hg
  refine ⟨∑ i ∈ Finset.range (k + 1), ((k.choose i : ℝ) * Cf i) * Cg (k - i),
    Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hCf0 i)) (hCg0 _),
    fun y hy => ?_⟩
  have hw : 0 ≤ (1 + |y 2|) ^ 3 := by positivity
  refine (mul_le_mul_of_nonneg_left
    (norm_iteratedFDeriv_mul_le hf hg y (by exact_mod_cast le_top)) hw).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  calc (1 + |y 2|) ^ 3 * ((k.choose i : ℝ) * ‖iteratedFDeriv ℝ i f y‖ *
        ‖iteratedFDeriv ℝ (k - i) g y‖)
      = ((k.choose i : ℝ) * ((1 + |y 2|) ^ 3 * ‖iteratedFDeriv ℝ i f y‖)) *
          ‖iteratedFDeriv ℝ (k - i) g y‖ := by ring
    _ ≤ ((k.choose i : ℝ) * Cf i) * Cg (k - i) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hCf i y hy) (Nat.cast_nonneg _)) (hCg _ y hy)
        (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hCf0 i))

theorem hjd3CompProj2 {W : ℝ} {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (Hg : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ, (1 + |z|) ^ 3 * ‖iteratedFDeriv ℝ k g z‖ ≤ C) :
    HeatJetDec3 W (fun y : Space => g (y 2)) := by
  intro k
  obtain ⟨Cg, hCg0, hCg⟩ := Hg k
  set P : Space →L[ℝ] ℝ := EuclideanSpace.proj (2 : Fin 3)
  have hfun : (fun y : Space => g (y 2)) = g ∘ P := by funext y; rfl
  refine ⟨Cg * ‖P‖ ^ k, mul_nonneg hCg0 (pow_nonneg (norm_nonneg _) _), fun y _ => ?_⟩
  rw [hfun, ContinuousLinearMap.iteratedFDeriv_comp_right P hg y (by exact_mod_cast le_top)]
  have h1 := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ k g (P y)) (fun _ : Fin k => P)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
  have hPy : P y = y 2 := rfl
  have hw : 0 ≤ (1 + |y 2|) ^ 3 := by positivity
  calc (1 + |y 2|) ^ 3 * ‖(iteratedFDeriv ℝ k g (P y)).compContinuousLinearMap fun _ => P‖
      ≤ (1 + |y 2|) ^ 3 * (‖iteratedFDeriv ℝ k g (P y)‖ * ‖P‖ ^ k) :=
        mul_le_mul_of_nonneg_left h1 hw
    _ = ((1 + |y 2|) ^ 3 * ‖iteratedFDeriv ℝ k g (y 2)‖) * ‖P‖ ^ k := by rw [hPy]; ring
    _ ≤ Cg * ‖P‖ ^ k := mul_le_mul_of_nonneg_right (hCg (y 2)) (pow_nonneg (norm_nonneg _) _)

/-- Weighted Gaussian jets: `(1 + |z|)³ ‖D^k g_ν^{(m)}(z)‖ ≤ C`. -/
theorem profileDeriv_wtd3 {ν : ℝ} (hν : 0 < ν) (m k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ,
      (1 + |z|) ^ 3 * ‖iteratedFDeriv ℝ k (UnforcedLeray.B0191.profileDeriv ν m) z‖ ≤ C := by
  obtain ⟨C0, hC0, h0⟩ := hfjProfileDeriv hν m k
  obtain ⟨M3, h3⟩ := UnforcedLeray.Heat.abs_wKer_le 3 (m + k) hν
  have hfun : UnforcedLeray.B0191.profile ν = UnforcedLeray.Heat.lineGauss ν := by
    funext x
    simp only [UnforcedLeray.B0191.profile, UnforcedLeray.B0191.heatKernel,
      UnforcedLeray.Heat.lineGauss, mul_one]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le)
      hν.le)]
    ring_nf
  set B3 : ℝ := max M3 0
  have hB3 : 0 ≤ B3 := le_max_right _ _
  refine ⟨4 * (C0 + B3), by positivity, fun z => ?_⟩
  have e : ‖iteratedFDeriv ℝ k (UnforcedLeray.B0191.profileDeriv ν m) z‖ =
      ‖iteratedDeriv (m + k) (UnforcedLeray.Heat.lineGauss ν) z‖ := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hfjProfileDerivEq ν k m]
    unfold UnforcedLeray.B0191.profileDeriv
    rw [hfun]
  have hz3 : |z| ^ 3 * ‖iteratedFDeriv ℝ k (UnforcedLeray.B0191.profileDeriv ν m) z‖ ≤ B3 := by
    rw [e, Real.norm_eq_abs, ← abs_pow, ← abs_mul]
    exact (h3 z).trans (le_max_left _ _)
  have hcub : (1 + |z|) ^ 3 ≤ 4 * (1 + |z| ^ 3) := by
    have ht : 0 ≤ |z| := abs_nonneg z
    have hdiff : 4 * (1 + |z| ^ 3) - (1 + |z|) ^ 3 = 3 * (|z| - 1) ^ 2 * (|z| + 1) := by ring
    have hnn : 0 ≤ 3 * (|z| - 1) ^ 2 * (|z| + 1) := by positivity
    linarith
  have h0z := h0 z
  have hnorm0 : 0 ≤ ‖iteratedFDeriv ℝ k (UnforcedLeray.B0191.profileDeriv ν m) z‖ := norm_nonneg _
  calc (1 + |z|) ^ 3 * ‖iteratedFDeriv ℝ k (UnforcedLeray.B0191.profileDeriv ν m) z‖
      ≤ 4 * (1 + |z| ^ 3) * ‖iteratedFDeriv ℝ k (UnforcedLeray.B0191.profileDeriv ν m) z‖ :=
        mul_le_mul_of_nonneg_right hcub hnorm0
    _ = 4 * (‖iteratedFDeriv ℝ k (UnforcedLeray.B0191.profileDeriv ν m) z‖ +
          |z| ^ 3 * ‖iteratedFDeriv ℝ k (UnforcedLeray.B0191.profileDeriv ν m) z‖) := by ring
    _ ≤ 4 * (C0 + B3) := by linarith

theorem hjd3ProfileDeriv {W : ℝ} {ν : ℝ} (hν : 0 < ν) (m : ℕ) :
    HeatJetDec3 W (fun y : Space => UnforcedLeray.B0191.profileDeriv ν m (y 2)) :=
  hjd3CompProj2 (UnforcedLeray.Short.IIb.contDiff_profileDeriv ν m)
    (fun k => profileDeriv_wtd3 hν m k)

theorem heatFieldDec3 {ν : ℝ} (hν : 0 < ν) (R : ℝ) (j : ℕ) (W : ℝ) :
    HeatJetDec3 W (heatField ν R j) := by
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
  have hA : HeatJetDec3 W (hfjA ν R j) := by
    unfold hfjA
    exact hjd3MulL (f := fun _ : Space => -((R ^ (2 * j + 1))⁻¹))
      (g := fun y : Space => (y 0 ^ 2 + y 1 ^ 2) ^ j *
        UnforcedLeray.B0191.profileDeriv ν (2 * j + 1) (y 2))
      contDiff_const (cwj.mul (cg (2 * j + 1))) (hfjConst _)
      (hjd3MulL cwj (cg (2 * j + 1)) hP (hjd3ProfileDeriv hν (2 * j + 1)))
  have hB : HeatJetDec3 W (hfjB ν R j) := by
    unfold hfjB
    exact hjd3MulL (f := fun _ : Space => (2 * (j : ℝ) + 2) * (R ^ (2 * j + 1))⁻¹)
      (g := fun y : Space => (y 0 ^ 2 + y 1 ^ 2) ^ j *
        UnforcedLeray.B0191.profileDeriv ν (2 * j) (y 2))
      contDiff_const (cwj.mul (cg (2 * j))) (hfjConst _)
      (hjd3MulL cwj (cg (2 * j)) hP (hjd3ProfileDeriv hν (2 * j)))
  have cA : ContDiff ℝ ∞ (hfjA ν R j) := by
    unfold hfjA
    exact contDiff_const.mul (cwj.mul (cg (2 * j + 1)))
  have cB : ContDiff ℝ ∞ (hfjB ν R j) := by
    unfold hfjB
    exact contDiff_const.mul (cwj.mul (cg (2 * j)))
  have hT0 : HeatJetDec3 W (fun y : Space => (hfjA ν R j y * y 0) • coordinateVector 0) :=
    hjd3SmulConst (cA.mul c0) (coordinateVector 0) (hjd3MulR cA c0 hA h0)
  have hT1 : HeatJetDec3 W (fun y : Space => (hfjA ν R j y * y 1) • coordinateVector 1) :=
    hjd3SmulConst (cA.mul c1) (coordinateVector 1) (hjd3MulR cA c1 hA h1)
  have hT2 : HeatJetDec3 W (fun y : Space => hfjB ν R j y • Axi.e3) :=
    hjd3SmulConst cB Axi.e3 hB
  have cT0 : ContDiff ℝ ∞ (fun y : Space => (hfjA ν R j y * y 0) • coordinateVector 0) :=
    (cA.mul c0).smul contDiff_const
  have cT1 : ContDiff ℝ ∞ (fun y : Space => (hfjA ν R j y * y 1) • coordinateVector 1) :=
    (cA.mul c1).smul contDiff_const
  have cT2 : ContDiff ℝ ∞ (fun y : Space => hfjB ν R j y • Axi.e3) :=
    cB.smul contDiff_const
  have hall : HeatJetDec3 W (fun y : Space => (hfjA ν R j y * y 0) • coordinateVector 0 +
      ((hfjA ν R j y * y 1) • coordinateVector 1 + hfjB ν R j y • Axi.e3)) :=
    hjd3Add cT0 (cT1.add cT2) hT0 (hjd3Add cT1 cT2 hT1 hT2)
  have hfun : heatField ν R j = fun y : Space => (hfjA ν R j y * y 0) • coordinateVector 0 +
      ((hfjA ν R j y * y 1) • coordinateVector 1 + hfjB ν R j y • Axi.e3) :=
    funext (hfjField ν R j)
  rw [hfun]
  exact hall

/-- Cubic axial decay of `heatSum` on `ϱ² ≤ W`: `(1 + |y₃|)³ ‖D^k heatSum(y)‖ ≤ C`. -/
theorem heatSumDec3 {ν : ℝ} (hν : 0 < ν) (R : ℝ) (a : ℕ → ℝ) (N : ℕ) (W : ℝ) :
    HeatJetDec3 W (heatSum ν R a N) := by
  intro k
  choose CH hCH0 hCH using fun j => heatFieldDec3 hν R j W k
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
  have hw : 0 ≤ (1 + |y 2|) ^ 3 := by positivity
  refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) hw).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [iteratedFDeriv_const_smul_apply'
      (((contDiff_heatField ν R j).contDiffAt (x := y)).of_le (m := (k : WithTop ℕ∞))
        (by exact_mod_cast le_top)),
    norm_smul, Real.norm_eq_abs]
  calc (1 + |y 2|) ^ 3 * (|a j| * ‖iteratedFDeriv ℝ k (heatField ν R j) y‖)
      = |a j| * ((1 + |y 2|) ^ 3 * ‖iteratedFDeriv ℝ k (heatField ν R j) y‖) := by ring
    _ ≤ |a j| * CH j := mul_le_mul_of_nonneg_left (hCH j y hy) (abs_nonneg _)

/-- Unconditional `TrainHeatRemWtd` from `RawAndInletL4`. -/
theorem trainHeatRemWtd_uncond : PartIIIb.Concrete.TrainHeatRemWtd := by
  have hF : PartIIIb.Concrete.WeightedTrainFluctAgeJetFixed :=
    PartIIIb.Concrete.weightedTrainFluctAgeJetFixed_of
      PartI.trainFluctAgeJetFixed fluctDoubledWeightPoly_proof
  exact PartIIIb.Concrete.trainHeatRemWtd_of PartI.trainStreamSmooth PartI.trainMeanEquations_proof
    heatTermSmooth
    (PartIIIb.Concrete.trainFluctWtdFixed_of PartI.trainStreamSmooth
      PartI.trainMeanEquations_proof PartI.jointFromAgeJets hF)
    (PartIIIb.Concrete.trainMeanRemWtdFixed_of PartI.trainMeanEquations_proof
      heatTermSmooth PartI.jointFromMixed1D weightedTrainMeanRemMixedFixed_proof)

/-- Near-axis (`1 < Axi.age p.R y`, `2 * p.R ≤ ‖y‖`) cubic decay `(1 + ‖y‖)³ ‖D^k (p.raw τ) y‖ ≤ B`
from `heatSumDec3` and `TrainHeatRemWtd` at transverse weight `k + 4`. -/
theorem raw_near_axis_decay3 :
    ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ (dm dp : ℝ) (p : UnforcedLeray.Cons.C03.Concrete.Params) (d : ℝ),
      BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∀ k : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ (τ : ℝ) (y : Space),
        y ∉ Axi.axis → 1 < Axi.age p.R y → 2 * p.R ≤ ‖y‖ →
        (1 + ‖y‖) ^ 3 * ‖iteratedFDeriv ℝ k (p.raw τ) y‖ ≤ B := by
  obtain ⟨νN, hνN, HN⟩ := trainHeatRemWtd_uncond 2 (by norm_num)
  refine ⟨νN, hνN, fun dm dp p d hreg hν k => ?_⟩
  have hν0 : 0 < p.ν := p.ν_pos
  have hc : p.c = UnforcedLeray.Short.PartI.trainPeriod 2 p.ν := by
    rw [hreg.c_eq]
    unfold UnforcedLeray.Short.PartI.trainPeriod
    rw [Real.rpow_neg hν0.le, Real.rpow_two]
  have htr : UnforcedLeray.Short.PartI.IsBUCTrain p.train := hreg.train_buc
  set Ψ : ℝ × (ℝ × ℝ) → ℝ := fun x => p.train.ψ x.1 x.2 with hΨdef
  have hΨ : ContDiffOn ℝ ∞ Ψ (Ioi 0 ×ˢ univ) := hreg.train_stream_smooth
  have hR1 : 1 ≤ p.R := RawAndInletL4.one_le_R_of hreg
  have hR0 : 0 < p.R := lt_of_lt_of_le one_pos hR1
  obtain ⟨Cn, Kn, hCn0, Hn⟩ := PartIIa.nv_jet_le_unif k
  set N : ℕ := Kn + k + 4 with hNdef
  set a : ℕ → ℝ := UnforcedLeray.Short.PartI.meanCoeff p.train with ha
  set ΦN : ℝ × (ℝ × ℝ) → ℝ := heatRemainder p.ν a N Ψ with hΦNdef
  have hNb : ∀ i : ℕ, ∃ C : ℝ, ∀ x : ℝ × (ℝ × ℝ), 1 ≤ x.1 →
      (1 + |x.2.2|) ^ (k + 4) * ‖iteratedFDeriv ℝ i ΦN x‖ ≤
        C * x.1 ^ (((k + 4 : ℕ) : ℝ) / 2 - N - 3 / 2) :=
    fun i => HN p.ν p.c hν0 hν hc p.train htr N (k + 4) i
  choose CN hCN using hNb
  obtain ⟨CH, hCH0, hCH⟩ := heatSumDec3 hν0 p.R a N (p.R ^ 2) k
  set SN : ℝ := ∑ i ∈ Finset.range (k + 2), |CN i| with hSN
  have hSN0 : 0 ≤ SN := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨8 * CH + 8 * Cn * 2 ^ (Kn + 1) * SN, by positivity, fun τ y hy hs1 hynorm => ?_⟩
  have hs : 0 < Axi.age p.R y := PartIIIb.Concrete.age_pos_of hR0 hy
  have hεR : p.ε = p.R⁻¹ := (inv_inv p.ε).symm
  have hprof : ∀ x : ℝ × (ℝ × ℝ), 0 < x.1 →
      UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ x =
        Axi.ringStreamProfile p.R Ψ x := by
    intro x hx
    rw [hεR, hΨdef]
    exact rawStreamProfile p.ν p.c p.R p.train hR0 hreg.train_stream_smooth x hx
  have hev : p.raw τ =ᶠ[𝓝 y] Axi.Nv p.R (Axi.ringStreamProfile p.R Ψ) τ := by
    filter_upwards [Axi.isOpen_compl_axis.mem_nhds hy] with z hz
    have e1 : p.raw τ z =
        Axi.Nv p.R (UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ) τ z :=
      p.raw_eq_off_axis τ z hz
    rw [e1]
    unfold Axi.Nv
    rw [hprof (Axi.chart p.R τ z) (PartIIIb.Concrete.age_pos_of hR0 hz)]
  rw [(hev.iteratedFDeriv ℝ k).eq_of_nhds]
  have hϱ0 : 0 < Axi.ϱ y := Axi.ϱ_pos hy
  have hϱ2 : Axi.ϱ y ^ 2 < p.R ^ 2 := by
    have h1 : 1 < p.R ^ 2 / Axi.ϱ y ^ 2 := hs1
    rwa [lt_div_iff₀ (pow_pos hϱ0 2), one_mul] at h1
  have hϱR : Axi.ϱ y ≤ p.R := by nlinarith
  have hny := RawAndInletL4.norm_le_ϱ_add y
  have hy2R : p.R ≤ |y 2| := by linarith
  have hw_norm : 1 + ‖y‖ ≤ 2 * (1 + |y 2|) := by linarith
  have hw1 : (1 + ‖y‖) ^ 3 ≤ 8 * (1 + |y 2|) ^ 3 := by
    calc (1 + ‖y‖) ^ 3 ≤ (2 * (1 + |y 2|)) ^ 3 := pow_le_pow_left₀ (by positivity) hw_norm 3
      _ = 8 * (1 + |y 2|) ^ 3 := by ring
  have hy2_eta : |y 2| ≤ |Axi.trans p.R y| := by
    have e : |Axi.trans p.R y| = p.R * |y 2| / Axi.ϱ y := by
      unfold Axi.trans
      rw [abs_div, abs_mul, abs_of_pos hR0, abs_of_pos hϱ0]
    rw [e, le_div_iff₀ hϱ0]
    nlinarith [abs_nonneg (y 2)]
  have hw2 : (1 + ‖y‖) ^ 3 ≤ 8 * (1 + |Axi.trans p.R y|) ^ 3 := by
    calc (1 + ‖y‖) ^ 3 ≤ 8 * (1 + |y 2|) ^ 3 := hw1
      _ ≤ 8 * (1 + |Axi.trans p.R y|) ^ 3 := by gcongr
  have hΦN : ContDiffOn ℝ ∞ ΦN (Ioi 0 ×ˢ univ) :=
    hΨ.sub (ContDiffOn.sum fun l _ => contDiffOn_const.mul (heatTermSmooth p.ν hν0 l))
  have hBN : ContDiffOn ℝ ∞ (Axi.ringStreamProfile p.R ΦN) (Ioi 0 ×ˢ univ) :=
    (PartIIIb.Concrete.ringProfileMeridJet p.R ΦN hΦN).1
  have hev2 : Axi.Nv p.R (Axi.ringStreamProfile p.R Ψ) τ =ᶠ[𝓝 y]
      PartIIIb.Concrete.heatSum p.ν p.R a N + Axi.Nv p.R (Axi.ringStreamProfile p.R ΦN) τ := by
    filter_upwards [Axi.isOpen_compl_axis.mem_nhds hy] with z hz
    exact PartIIIb.Concrete.Nv_heat_decomp hν0 hR0 a N hΨ τ hz
  obtain ⟨_, _, _, HJ⟩ := PartIIIb.Concrete.ringLiftPtJet k
  have hNvc : ContDiffAt ℝ k (Axi.Nv p.R (Axi.ringStreamProfile p.R ΦN) τ) y :=
    (((HJ p.R τ _ hR1 hBN).1).contDiffAt (Axi.isOpen_compl_axis.mem_nhds hy)).of_le
      (by exact_mod_cast le_top)
  have hHc : ContDiffAt ℝ k (PartIIIb.Concrete.heatSum p.ν p.R a N) y :=
    (PartIIIb.Concrete.contDiff_heatSum p.ν p.R a N).contDiffAt.of_le
      (by exact_mod_cast le_top)
  rw [(hev2.iteratedFDeriv ℝ k).eq_of_nhds, iteratedFDeriv_add_apply hHc hNvc]
  have hheat : (1 + ‖y‖) ^ 3 * ‖iteratedFDeriv ℝ k (PartIIIb.Concrete.heatSum p.ν p.R a N) y‖ ≤
      8 * CH := by
    calc (1 + ‖y‖) ^ 3 * ‖iteratedFDeriv ℝ k (PartIIIb.Concrete.heatSum p.ν p.R a N) y‖
        ≤ (8 * (1 + |y 2|) ^ 3) *
            ‖iteratedFDeriv ℝ k (PartIIIb.Concrete.heatSum p.ν p.R a N) y‖ :=
          mul_le_mul_of_nonneg_right hw1 (norm_nonneg _)
      _ = 8 * ((1 + |y 2|) ^ 3 *
            ‖iteratedFDeriv ℝ k (PartIIIb.Concrete.heatSum p.ν p.R a N) y‖) := by ring
      _ ≤ 8 * CH := mul_le_mul_of_nonneg_left (hCH y hϱ2.le) (by norm_num)
  have h2 := Hn p.R ΦN hR1 hΦN τ y hy
  set s := Axi.age p.R y
  set η := |Axi.trans p.R y|
  have hs1' : 1 ≤ s := hs1.le
  set e : ℝ := ((k + 4 : ℕ) : ℝ) / 2 - N - 3 / 2 with hedef
  have hrpow0 : 0 ≤ s ^ e := Real.rpow_nonneg hs.le _
  have hsumN : (1 + η) ^ (k + 4) *
      ∑ i ∈ Finset.range (k + 2), ‖iteratedFDeriv ℝ i ΦN (Axi.chart p.R τ y)‖ ≤ SN * s ^ e := by
    rw [Finset.mul_sum, hSN, Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    exact (hCN i (Axi.chart p.R τ y) hs1').trans
      (mul_le_mul_of_nonneg_right (le_abs_self _) hrpow0)
  have he : e ≤ -((Kn + 1 : ℕ) : ℝ) := by
    rw [hedef, hNdef]; push_cast; linarith
  have hpow : (1 + s) ^ (Kn + 1) * s ^ e ≤ 2 ^ (Kn + 1) := by
    have h2s : (1 + s) ^ (Kn + 1) ≤ 2 ^ (Kn + 1) * s ^ (Kn + 1) := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by linarith) (by linarith) _
    have hle1 : s ^ (Kn + 1) * s ^ e ≤ 1 := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hs]
      exact Real.rpow_le_one_of_one_le_of_nonpos hs1' (by push_cast at he ⊢; linarith)
    calc (1 + s) ^ (Kn + 1) * s ^ e ≤ 2 ^ (Kn + 1) * s ^ (Kn + 1) * s ^ e :=
          mul_le_mul_of_nonneg_right h2s hrpow0
      _ = 2 ^ (Kn + 1) * (s ^ (Kn + 1) * s ^ e) := by ring
      _ ≤ 2 ^ (Kn + 1) * 1 := mul_le_mul_of_nonneg_left hle1 (by positivity)
      _ = 2 ^ (Kn + 1) := mul_one _
  have hrem : (1 + ‖y‖) ^ 3 *
      ‖iteratedFDeriv ℝ k (Axi.Nv p.R (Axi.ringStreamProfile p.R ΦN) τ) y‖ ≤
      8 * Cn * 2 ^ (Kn + 1) * SN := by
    have hw_pow : (1 + η) ^ 3 * (1 + η) ^ (k + 1) = (1 + η) ^ (k + 4) := by
      rw [← pow_add]; congr 1; omega
    calc (1 + ‖y‖) ^ 3 *
          ‖iteratedFDeriv ℝ k (Axi.Nv p.R (Axi.ringStreamProfile p.R ΦN) τ) y‖
        ≤ (8 * (1 + η) ^ 3) * (Cn * (1 + s) ^ (Kn + 1) * ((1 + η) ^ (k + 1) *
            ∑ i ∈ Finset.range (k + 2), ‖iteratedFDeriv ℝ i ΦN (Axi.chart p.R τ y)‖)) :=
          mul_le_mul hw2 h2 (norm_nonneg _) (by positivity)
      _ = 8 * Cn * (1 + s) ^ (Kn + 1) * (((1 + η) ^ 3 * (1 + η) ^ (k + 1)) *
            ∑ i ∈ Finset.range (k + 2), ‖iteratedFDeriv ℝ i ΦN (Axi.chart p.R τ y)‖) := by ring
      _ = 8 * Cn * (1 + s) ^ (Kn + 1) * ((1 + η) ^ (k + 4) *
            ∑ i ∈ Finset.range (k + 2), ‖iteratedFDeriv ℝ i ΦN (Axi.chart p.R τ y)‖) := by
          rw [hw_pow]
      _ ≤ 8 * Cn * (1 + s) ^ (Kn + 1) * (SN * s ^ e) :=
          mul_le_mul_of_nonneg_left hsumN (by positivity)
      _ = 8 * Cn * SN * ((1 + s) ^ (Kn + 1) * s ^ e) := by ring
      _ ≤ 8 * Cn * SN * 2 ^ (Kn + 1) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = 8 * Cn * 2 ^ (Kn + 1) * SN := by ring
  have hy0 : 0 ≤ (1 + ‖y‖) ^ 3 := by positivity
  calc (1 + ‖y‖) ^ 3 * ‖iteratedFDeriv ℝ k (PartIIIb.Concrete.heatSum p.ν p.R a N) y +
        iteratedFDeriv ℝ k (Axi.Nv p.R (Axi.ringStreamProfile p.R ΦN) τ) y‖
      ≤ (1 + ‖y‖) ^ 3 * (‖iteratedFDeriv ℝ k (PartIIIb.Concrete.heatSum p.ν p.R a N) y‖ +
          ‖iteratedFDeriv ℝ k (Axi.Nv p.R (Axi.ringStreamProfile p.R ΦN) τ) y‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) hy0
    _ = (1 + ‖y‖) ^ 3 * ‖iteratedFDeriv ℝ k (PartIIIb.Concrete.heatSum p.ν p.R a N) y‖ +
          (1 + ‖y‖) ^ 3 *
            ‖iteratedFDeriv ℝ k (Axi.Nv p.R (Axi.ringStreamProfile p.R ΦN) τ) y‖ := by ring
    _ ≤ 8 * CH + 8 * Cn * 2 ^ (Kn + 1) * SN := add_le_add hheat hrem

end UnforcedLeray.Short.IIb.RawHeatAux
